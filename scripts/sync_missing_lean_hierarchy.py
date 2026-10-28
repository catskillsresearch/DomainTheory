#!/usr/bin/env python3
"""Link every ``DomainTheory/**/*.lean`` into the ``DomainTheory.md`` note tree.

Uses Lean import edges to attach modules that are not yet cited in any note,
places each on the same note as its earliest importer (after relocation), and
rewrites notes with ``**[label](path)**`` + ``@import "rel.lean"`` blocks in
dependency order (dependencies before first use).
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DT = ROOT / "DomainTheory"
ENTRY = ROOT / "DomainTheory.md"

sys.path.insert(0, str(Path(__file__).resolve().parent))
from compile_md_tree import (  # noqa: E402
    DEFAULT_ROOT_MD,
    child_md_targets,
    lean_targets_in_note_text,
)
from order_lean_links import (  # noqa: E402
    blockers,
    is_aggregator,
    module_name,
    raw_imports,
    relocate,
    topo_sort,
)

IMPORT = re.compile(
    r"^(?:public\s+|private\s+|meta\s+)?import\s+(?:all\s+)?(DomainTheory\.[^\s]+)"
)
LEAN_BLOCK_RE = re.compile(
    r"\*\*\[(?P<label>[^\]]*)\]\((?P<link>[^)]+\.lean)\)\*\*\n+"
    r'@import\s+"(?P<imp>[^"]+\.lean)"\s*\n',
)
NOTE_STEM_RE = re.compile(r"(?:1972|1976|1980|1982)_")


def load_modules() -> dict[str, Path]:
    out: dict[str, Path] = {}
    for path in DT.rglob("*.lean"):
        try:
            if path.is_file():
                out[module_name(path)] = path.resolve()
        except OSError:
            continue
    return out


def outline_toc(
    root_md: Path,
    modules: dict[str, Path],
) -> tuple[list[Path], dict[str, Path], dict[str, str], dict[str, int]]:
    note_order: list[Path] = []
    owner: dict[str, Path] = {}
    labels: dict[str, str] = {}
    seen_index: dict[str, int] = {}
    seen_notes: set[Path] = set()
    counter = 0

    def walk(note: Path) -> None:
        nonlocal counter
        resolved = note.resolve()
        if resolved in seen_notes:
            return
        seen_notes.add(resolved)
        note_order.append(resolved)
        raw = resolved.read_text(encoding="utf-8")
        for path in lean_targets_in_note_text(resolved, raw):
            mod = module_name(path)
            if mod not in owner:
                owner[mod] = resolved
                labels[mod] = path.stem
                seen_index[mod] = counter
                counter += 1
        for _indent, _title, child in child_md_targets(resolved, raw):
            walk(child)

    if not root_md.is_file():
        raise FileNotFoundError(root_md)
    walk(root_md.resolve())
    return note_order, owner, labels, seen_index


def fallback_note(mod: str, modules: dict[str, Path], note_order: list[Path]) -> Path:
    path = modules[mod]
    lean_dir = path.parent.resolve()
    same_dir = [n for n in note_order if n.parent.resolve() == lean_dir]
    if same_dir:

        def rank(n: Path) -> tuple[int, str]:
            return (0 if NOTE_STEM_RE.search(n.name) else 1, n.name)

        return sorted(same_dir, key=rank)[0]

    lean_parts = path.relative_to(DT).parts[:-1]
    best: Path | None = None
    best_common = -1
    for note in note_order:
        try:
            note_parts = note.relative_to(DT).parts[:-1]
        except ValueError:
            continue
        common = 0
        for a, b in zip(note_parts, lean_parts):
            if a == b:
                common += 1
            else:
                break
        if common > best_common:
            best_common = common
            best = note
    if best is not None:
        return best
    return note_order[0]


def attach_missing_modules(
    modules: dict[str, Path],
    imports_of: dict[str, list[str]],
    note_order: list[Path],
    owner: dict[str, Path],
    labels: dict[str, str],
    seen_index: dict[str, int],
) -> int:
    missing = set(modules) - set(owner)
    counter = max(seen_index.values(), default=-1) + 1
    added = 0
    while missing:
        progress = False
        for mod in sorted(missing):
            importers = [v for v in modules if mod in imports_of.get(v, ())]
            ready = [v for v in importers if v in owner]
            if not ready:
                continue
            anchor = min(ready, key=lambda v: seen_index[v])
            owner[mod] = owner[anchor]
            labels.setdefault(mod, modules[mod].stem)
            seen_index[mod] = counter
            counter += 1
            missing.remove(mod)
            added += 1
            progress = True
        if progress:
            continue
        if not missing:
            break
        mod = min(missing)
        owner[mod] = fallback_note(mod, modules, note_order)
        labels.setdefault(mod, modules[mod].stem)
        seen_index[mod] = counter
        counter += 1
        missing.remove(mod)
        added += 1
    return added


def resolve_link_to_mod(link: str, note: Path, modules: dict[str, Path]) -> str | None:
    href = link.strip().split("#", 1)[0]
    if href.startswith("DomainTheory/"):
        target = (ROOT / href).resolve()
    else:
        target = (note.parent / href).resolve()
        if not target.is_file():
            target = (ROOT / href).resolve()
    if not target.is_file():
        return None
    mod = module_name(target)
    return mod if mod in modules else None


def format_lean_block(note: Path, mod_path: Path, label: str) -> str:
    rel_repo = mod_path.relative_to(ROOT).as_posix()
    try:
        label_href = mod_path.relative_to(DT).as_posix()
    except ValueError:
        label_href = rel_repo
    rel_import = Path(os.path.relpath(mod_path, note.parent)).as_posix()
    return (
        f"**[{label_href}]({rel_repo})**\n\n"
        f'@import "{rel_import}"\n'
    )


def find_insert_pos(text: str) -> int:
    """Where to put lean blocks when a note has none yet."""
    lines = text.splitlines(keepends=True)
    pos = 0
    last_english = 0
    for i, line in enumerate(lines):
        pos += len(line)
        if re.match(r'^@import\s+"[^"]+\.english"', line):
            last_english = pos
    if last_english:
        return last_english
    for i, line in enumerate(lines):
        if line.startswith("#"):
            return sum(len(lines[j]) for j in range(i + 1))
    return len(text)


def rewrite_note_lean_blocks(
    note: Path,
    ordered_mods: list[str],
    modules: dict[str, Path],
    labels: dict[str, str],
    *,
    dry_run: bool,
) -> bool:
    if not ordered_mods:
        return False
    text = note.read_text(encoding="utf-8")
    spans: list[tuple[int, int, str, str]] = []
    for m in LEAN_BLOCK_RE.finditer(text):
        mod = resolve_link_to_mod(m.group("link"), note, modules)
        if mod is None:
            continue
        spans.append((m.start(), m.end(), mod, m.group(0)))
    existing_blob = {mod: blob for _s, _e, mod, blob in spans}

    new_blobs: list[str] = []
    for mod in ordered_mods:
        if mod in existing_blob:
            new_blobs.append(existing_blob[mod])
        else:
            new_blobs.append(format_lean_block(note, modules[mod], labels[mod]))

    if spans:
        old_order = [mod for _s, _e, mod, _b in spans]
        if old_order == ordered_mods and len(ordered_mods) == len(spans):
            return False
    else:
        if not any(mod not in existing_blob for mod in ordered_mods):
            return False

    if dry_run:
        return True

    stripped = text
    for start, end, _mod, _blob in sorted(spans, key=lambda t: t[0], reverse=True):
        stripped = stripped[:start] + stripped[end:]

    insert_at = spans[0][0] if spans else find_insert_pos(stripped)
    insertion = "".join(new_blobs)
    if insert_at <= len(stripped) and not stripped[insert_at - 1 : insert_at].endswith("\n"):
        insertion = "\n" + insertion
    new_text = stripped[:insert_at] + insertion + stripped[insert_at:]
    new_text = re.sub(r"\n{4,}", "\n\n\n", new_text)
    if not new_text.endswith("\n"):
        new_text += "\n"
    note.write_text(new_text, encoding="utf-8")
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT_MD)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    modules = load_modules()
    aggregators = {mod for mod, path in modules.items() if is_aggregator(path)}
    imports_of = {mod: raw_imports(path, modules) for mod, path in modules.items()}

    note_order, owner, labels, seen_index = outline_toc(args.root.resolve(), modules)
    before_count = len(owner)
    added = attach_missing_modules(
        modules, imports_of, note_order, owner, labels, seen_index
    )
    note_time = {note: idx for idx, note in enumerate(note_order)}
    relocate(modules, aggregators, owner, note_time, imports_of)

    by_note: dict[Path, list[str]] = defaultdict(list)
    for mod, note in owner.items():
        by_note[note].append(mod)

    for note, mods in by_note.items():
        edges = {
            mod: {
                dep
                for dep in blockers(mod, modules, aggregators, owner, imports_of)
                if dep in mods
            }
            for mod in mods
        }
        by_note[note] = topo_sort(mods, edges, seen_index)

    touched = 0
    for note, mods in by_note.items():
        if rewrite_note_lean_blocks(
            note, mods, modules, labels, dry_run=args.dry_run
        ):
            touched += 1

    print(
        f"Linked modules: {before_count} → {len(owner)} (+{added} new assignments); "
        f"rewrote {touched} notes"
        + (" (dry run)" if args.dry_run else "")
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
