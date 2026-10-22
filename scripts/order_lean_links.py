#!/usr/bin/env python3
"""Place each linked Lean file after the files it imports, in outline order.

Outline order is a depth-first walk of markdown bullet links from
DomainTheory.md (prose cross-references are not followed). A non-aggregator
file is blocked only by the non-aggregator modules it imports directly. An
aggregator (a module with no declarations) is blocked by every module it
imports, so it is inlined after the pieces it re-exports. Files that would
appear before a blocker are moved onto that blocker's note, and each note's
Lean list is topologically sorted.
"""

from __future__ import annotations

import os
import re
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DT = ROOT / "DomainTheory"
ENTRY = ROOT / "DomainTheory.md"

LINK = re.compile(r"\[([^\]]*)\]\(([^)]+)\)")
BULLET_MD = re.compile(r"^\s*-\s+\[[^\]]*\]\(([^)]+)\)\s*$")
LEAN_BULLET = re.compile(r"^(\s*)-\s+\[([^\]]*)\]\(([^)]+\.lean)\)\s*$")
FENCE = re.compile(r"^\s*(`{3,})")
IMPORT = re.compile(
    r"^(?:public\s+|private\s+|meta\s+)?import\s+(?:all\s+)?(DomainTheory\.[^\s]+)"
)
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom)\b"
)


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def load_modules() -> dict[str, Path]:
    return {module_name(path): path for path in DT.rglob("*.lean")}


def is_aggregator(path: Path) -> bool:
    for line in path.read_text(encoding="utf-8").splitlines():
        if DECL.match(line.strip()):
            return False
    return True


def raw_imports(path: Path, modules: dict[str, Path]) -> list[str]:
    found: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT.match(line.strip())
        if match and match.group(1) in modules:
            found.append(match.group(1))
    return found


def resolve_md(base: Path, href: str) -> Path | None:
    path = href.strip().split("#", 1)[0]
    if not path.endswith(".md"):
        return None
    target = (base.parent / path).resolve()
    try:
        target.relative_to(ROOT)
    except ValueError:
        return None
    return target if target.is_file() else None


def resolve_lean(base: Path, href: str) -> Path | None:
    path = href.strip().split("#", 1)[0]
    if not path.endswith(".lean") or "://" in path:
        return None
    target = (base.parent / path).resolve()
    if target.is_file():
        return target
    rooted = (ROOT / path).resolve()
    return rooted if rooted.is_file() else None


def outline(modules: dict[str, Path]) -> tuple[list[Path], dict[str, Path], dict[str, str], dict[str, int]]:
    """Return note order, first owner, label, and first-seen index for each module."""
    note_order: list[Path] = []
    owner: dict[str, Path] = {}
    labels: dict[str, str] = {}
    seen_index: dict[str, int] = {}
    seen_notes: set[Path] = set()
    counter = 0

    def walk(note: Path) -> None:
        nonlocal counter
        if note in seen_notes or not note.is_file():
            return
        seen_notes.add(note)
        note_order.append(note)
        text = note.read_text(encoding="utf-8")
        in_fence = False
        respect = sum(1 for line in text.splitlines() if FENCE.match(line)) % 2 == 0
        bullets: list[Path] = []
        for line in text.splitlines():
            fence = FENCE.match(line) if respect else None
            if fence is not None:
                if not in_fence:
                    in_fence = True
                elif line.lstrip().startswith(fence.group(1)):
                    in_fence = False
                continue
            if in_fence:
                continue
            bullet = BULLET_MD.match(line)
            if bullet:
                child = resolve_md(note, bullet.group(1))
                if child is not None:
                    bullets.append(child)
            for match in LINK.finditer(line):
                lean = resolve_lean(note, match.group(2))
                if lean is None:
                    continue
                mod = module_name(lean)
                if mod not in owner:
                    owner[mod] = note
                    labels[mod] = match.group(1)
                    seen_index[mod] = counter
                    counter += 1
        for child in bullets:
            walk(child)

    walk(ENTRY.resolve())
    return note_order, owner, labels, seen_index


def blockers(
    mod: str,
    modules: dict[str, Path],
    aggregators: set[str],
    owner: dict[str, Path],
    imports_of: dict[str, list[str]],
) -> list[str]:
    imported = [dep for dep in imports_of[mod] if dep in owner]
    if mod in aggregators:
        return imported
    return [dep for dep in imported if dep not in aggregators]


def relocate(
    modules: dict[str, Path],
    aggregators: set[str],
    owner: dict[str, Path],
    note_time: dict[Path, int],
    imports_of: dict[str, list[str]],
) -> int:
    moves = 0
    for _ in range(32):
        changed = 0
        for mod in list(owner):
            deps = blockers(mod, modules, aggregators, owner, imports_of)
            if not deps:
                continue
            latest = max(deps, key=lambda dep: note_time[owner[dep]])
            if note_time[owner[mod]] < note_time[owner[latest]]:
                owner[mod] = owner[latest]
                changed += 1
        moves += changed
        if not changed:
            return moves
    raise SystemExit("lean-link relocation did not stabilize")


def topo_sort(mods: list[str], edges: dict[str, set[str]], tie: dict[str, int]) -> list[str]:
    """edges[mod] = blockers that must precede mod. Return mods in that order."""
    remaining = set(mods)
    incoming: dict[str, set[str]] = {mod: set() for mod in mods}
    for mod in mods:
        for dep in edges.get(mod, ()):
            if dep in remaining:
                incoming[mod].add(dep)
    ordered: list[str] = []
    while remaining:
        ready = sorted((mod for mod in remaining if not incoming[mod]), key=lambda mod: tie.get(mod, 0))
        if not ready:
            # A cycle among files on one note: keep the leftover in tie order.
            ready = sorted(remaining, key=lambda mod: tie.get(mod, 0))
            ordered.extend(ready)
            break
        chosen = ready[0]
        ordered.append(chosen)
        remaining.remove(chosen)
        for mod in remaining:
            incoming[mod].discard(chosen)
    return ordered


def rewrite(note: Path, ordered_mods: list[str], labels: dict[str, str], modules: dict[str, Path]) -> None:
    lines = note.read_text(encoding="utf-8").splitlines()
    kept: list[str] = []
    first_at: int | None = None
    for line in lines:
        match = LEAN_BULLET.match(line)
        if match and "://" not in match.group(3):
            if first_at is None:
                first_at = len(kept)
            continue
        kept.append(line)
    bullets = []
    for mod in ordered_mods:
        href = Path(os.path.relpath(modules[mod], note.parent)).as_posix()
        bullets.append(f"- [{labels[mod]}]({href})")
    if not bullets:
        # Drop a Lean 4 heading that no longer introduces anything.
        cleaned: list[str] = []
        index = 0
        while index < len(kept):
            if kept[index].strip() == "**Lean 4**":
                look = index + 1
                while look < len(kept) and kept[look].strip() == "":
                    look += 1
                if look >= len(kept) or kept[look].startswith("#"):
                    index = look
                    continue
            cleaned.append(kept[index])
            index += 1
        text = "\n".join(cleaned).rstrip() + "\n"
        note.write_text(text, encoding="utf-8")
        return
    block = bullets
    if first_at is None:
        if kept and kept[-1].strip() != "**Lean 4**":
            if kept and kept[-1].strip() != "":
                kept.append("")
            kept.append("**Lean 4**")
            kept.append("")
        kept.extend(block)
    else:
        kept[first_at:first_at] = block
    text = "\n".join(kept).rstrip() + "\n"
    note.write_text(text, encoding="utf-8")


def main() -> None:
    modules = load_modules()
    aggregators = {mod for mod, path in modules.items() if is_aggregator(path)}
    imports_of = {mod: raw_imports(path, modules) for mod, path in modules.items()}
    note_order, owner, labels, seen_index = outline(modules)
    note_time = {note: index for index, note in enumerate(note_order)}
    before = dict(owner)
    moves = relocate(modules, aggregators, owner, note_time, imports_of)

    by_note: dict[Path, list[str]] = defaultdict(list)
    for mod, note in owner.items():
        by_note[note].append(mod)

    for note, mods in by_note.items():
        edges = {
            mod: {dep for dep in blockers(mod, modules, aggregators, owner, imports_of) if dep in mods}
            for mod in mods
        }
        by_note[note] = topo_sort(mods, edges, seen_index)

    touched: set[Path] = set(before.values()) | set(owner.values())
    for note in touched:
        rewrite(note, by_note.get(note, []), labels, modules)

    moved = sum(1 for mod in before if owner[mod] != before[mod])
    print(f"moved {moved} Lean links across notes ({moves} relocation steps); rewrote {len(touched)} notes")


if __name__ == "__main__":
    main()
