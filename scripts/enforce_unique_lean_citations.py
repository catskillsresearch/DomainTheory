#!/usr/bin/env python3
"""Ensure each ``DomainTheory/**/*.lean`` is cited from exactly one hierarchy note.

Uses the same owner assignment as ``sync_missing_lean_hierarchy.py`` (outline
first-seen, attach importers, ``order_lean_links.relocate``), strips Lean link /
``@import`` blocks from non-owner notes, then rewrites owner notes in dependency
order.
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
    resolve_lean_target,
)
from order_lean_links import (  # noqa: E402
    blockers,
    is_aggregator,
    module_name,
    raw_imports,
    relocate,
    topo_sort,
)
from sync_missing_lean_hierarchy import (  # noqa: E402
    attach_missing_modules,
    find_insert_pos,
    format_lean_block,
    load_modules,
    outline_toc,
    resolve_link_to_mod,
    rewrite_note_lean_blocks,
)

LEAN_BLOCK_RE = re.compile(
    r"\*\*\[(?P<label>[^\]]*)\]\((?P<link>[^)]+\.lean)\)\*\*\n+"
    r'@import\s+"(?P<imp>[^"]+\.lean)"\s*\n',
)
IMPORT_LINE_RE = re.compile(r'^@import\s+"([^"]+\.lean)"\s*\n', re.MULTILINE)
BOLD_LEAN_LINE_RE = re.compile(
    r"^\s*\*\*\[[^\]]*\]\(([^)]+\.lean)\)\*\*\s*\n",
    re.MULTILINE,
)
NOTE_YEAR_STEM = re.compile(r"^(?:1972|1976|1980|1982)_(.+)$")

# Lean stem → ``1976_*.md`` note stem when prose title ≠ module name (same parent dir).
DEDICATED_NOTE_STEMS: dict[str, str] = {
    "Ycomb": "1976_Combinator_Y",
    "distributive_functions": "1976_Distributive_functions",
    "primitive_recursion": "1976_Primitive_recursion",
    "theorem_2_6": "1976_Definability",
    "IsRE": "1976_IsRE",
    "eSubset": "1976_Finite_subsets",
    "pairTerm": "1976_Pairing_terms",
    "mem_graph_const_iff": "1976_Constant_graph",
    "enumFun": "1976_Code_enumerator",
    "applyNat": "1976_Application",
    "num": "1976_Numerals",
}


def _norm_stem(s: str) -> str:
    return s.lower().replace("_", "")


def dedicated_note_for(
    mod: str, modules: dict[str, Path], notes: list[Path]
) -> Path | None:
    """Prefer ``1976_Theorem_2_1.md``-style notes over import-relocation hubs."""
    path = modules[mod]
    stem = path.stem
    parent = path.parent.resolve()
    alias_stem = DEDICATED_NOTE_STEMS.get(stem)
    if alias_stem is not None:
        for note in notes:
            if note.parent.resolve() == parent and note.stem == alias_stem:
                return note.resolve()
        for note in notes:
            if note.stem == alias_stem:
                return note.resolve()
    target = _norm_stem(stem)
    for note in notes:
        if note.parent.resolve() != parent:
            continue
        m = NOTE_YEAR_STEM.match(note.stem)
        if not m:
            continue
        if _norm_stem(m.group(1)) == target:
            return note.resolve()
    return None


def prefer_dedicated_notes(
    owner: dict[str, Path],
    modules: dict[str, Path],
    notes: list[Path],
) -> int:
    moved = 0
    for mod in modules:
        dedicated = dedicated_note_for(mod, modules, notes)
        if dedicated is None:
            continue
        if owner.get(mod) != dedicated:
            owner[mod] = dedicated
            moved += 1
    return moved


def owned_mods_on_note(note: Path, owner: dict[str, Path]) -> set[str]:
    return {mod for mod, n in owner.items() if n.resolve() == note.resolve()}


def strip_non_owned(note: Path, owner: dict[str, Path], modules: dict[str, Path]) -> bool:
    """Remove Lean citations for modules whose canonical note is elsewhere."""
    owned = owned_mods_on_note(note, owner)
    text = note.read_text(encoding="utf-8")
    original = text

    def keep_mod(mod: str | None) -> bool:
        return mod is not None and mod in owned

    spans: list[tuple[int, int]] = []
    for m in LEAN_BLOCK_RE.finditer(text):
        mod = resolve_link_to_mod(m.group("link"), note, modules)
        if mod is not None and not keep_mod(mod):
            spans.append((m.start(), m.end()))

    stripped = text
    for start, end in sorted(spans, key=lambda t: t[0], reverse=True):
        stripped = stripped[:start] + stripped[end:]

    def drop_import(m: re.Match[str]) -> str:
        rel = m.group(1)
        target = resolve_lean_target(note, rel)
        if not target.is_file():
            return m.group(0)
        mod = module_name(target)
        if mod in modules and mod not in owned:
            return ""
        return m.group(0)

    stripped = IMPORT_LINE_RE.sub(drop_import, stripped)

    def drop_bold(m: re.Match[str]) -> str:
        target = resolve_lean_target(note, m.group(1))
        if not target.is_file():
            return m.group(0)
        mod = module_name(target)
        if mod in modules and mod not in owned:
            return ""
        return m.group(0)

    stripped = BOLD_LEAN_LINE_RE.sub(drop_bold, stripped)
    stripped = re.sub(r"\n{4,}", "\n\n\n", stripped)
    if stripped != original:
        if not stripped.endswith("\n"):
            stripped += "\n"
        note.write_text(stripped, encoding="utf-8")
        return True
    return False


def collect_notes(root_md: Path) -> list[Path]:
    order: list[Path] = []
    seen: set[Path] = set()

    def walk(note: Path) -> None:
        resolved = note.resolve()
        if resolved in seen:
            return
        seen.add(resolved)
        order.append(resolved)
        raw = note.read_text(encoding="utf-8")
        for _indent, _title, child in child_md_targets(resolved, raw):
            walk(child)

    walk(root_md.resolve())
    return order


def verify(owner: dict[str, Path], modules: dict[str, Path], notes: list[Path]) -> tuple[int, int]:
    on_disk = {modules[m].resolve() for m in modules}
    cited: dict[Path, list[Path]] = defaultdict(list)
    for note in notes:
        raw = note.read_text(encoding="utf-8")
        for path in lean_targets_in_note_text(note, raw):
            cited[path.resolve()].append(note)
    missing = on_disk - set(cited)
    dups = {p: ns for p, ns in cited.items() if len(ns) > 1}
    return len(missing), len(dups)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT_MD)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    modules = load_modules()
    aggregators = {mod for mod, path in modules.items() if is_aggregator(path)}
    imports_of = {mod: raw_imports(path, modules) for mod, path in modules.items()}

    note_order, owner, labels, seen_index = outline_toc(args.root.resolve(), modules)
    attach_missing_modules(
        modules, imports_of, note_order, owner, labels, seen_index
    )
    note_time = {note: idx for idx, note in enumerate(note_order)}
    relocate(modules, aggregators, owner, note_time, imports_of)

    notes = collect_notes(args.root.resolve())
    dedicated_moves = prefer_dedicated_notes(owner, modules, notes)
    note_set = set(notes)

    if args.dry_run:
        missing, dups = verify(owner, modules, notes)
        print(
            f"Would enforce {len(owner)} owners ({dedicated_moves} dedicated-note overrides); "
            f"missing={missing} dups={dups}"
        )
        return 1 if missing or dups else 0

    stripped_count = 0
    for note in notes:
        if strip_non_owned(note, owner, modules):
            stripped_count += 1

    by_note: dict[Path, list[str]] = defaultdict(list)
    for mod, note in owner.items():
        if note.resolve() in note_set:
            by_note[note.resolve()].append(mod)

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

    rewritten = 0
    for note, mods in by_note.items():
        if rewrite_note_lean_blocks(
            Path(note), mods, modules, labels, dry_run=False
        ):
            rewritten += 1

    missing, dups = verify(owner, modules, notes)
    print(
        f"Stripped {stripped_count} notes; rewrote {rewritten} owner notes "
        f"({dedicated_moves} dedicated-note overrides); "
        f"missing={missing} duplicate modules={dups}"
    )
    return 1 if missing or dups else 0


if __name__ == "__main__":
    raise SystemExit(main())
