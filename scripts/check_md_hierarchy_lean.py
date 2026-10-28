#!/usr/bin/env python3
"""Fail unless every ``DomainTheory/**/*.lean`` is linked from the ``DomainTheory.md`` note tree.

Hierarchy = depth-first walk of TOC bullet / numbered-list links (same as
``compile_md_tree.py``). A module counts if some visited note contains a
markdown link to the ``.lean`` file or an ``@import "….lean"`` line.
"""
from __future__ import annotations

import argparse
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DT = ROOT / "DomainTheory"
DEFAULT_ROOT = ROOT / "DomainTheory.md"

sys.path.insert(0, str(Path(__file__).resolve().parent))
from compile_md_tree import collect_md_hierarchy_lean  # noqa: E402


def all_domain_lean() -> set[Path]:
    out: set[Path] = set()
    for path in DT.rglob("*.lean"):
        try:
            if path.is_file():
                out.add(path.resolve())
        except OSError:
            continue
    return out


def top_chapter(path: Path) -> str:
    rel = path.relative_to(DT)
    return rel.parts[0] if rel.parts else "?"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=DEFAULT_ROOT,
        help="root note (default: DomainTheory.md)",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="print every missing module path",
    )
    args = parser.parse_args()

    notes, linked = collect_md_hierarchy_lean(args.root.resolve())
    on_disk = all_domain_lean()
    missing = sorted(on_disk - linked, key=lambda p: p.as_posix())
    extra = sorted(linked - on_disk, key=lambda p: p.as_posix())

    print(
        f"Notes in hierarchy: {len(notes)}\n"
        f"Lean linked from notes: {len(linked)}\n"
        f"Lean on disk under DomainTheory/: {len(on_disk)}"
    )

    if extra:
        print(f"\nWarning: {len(extra)} linked paths outside DomainTheory/ (ignored for pass/fail)")

    if not missing:
        print(f"OK: every DomainTheory/**/*.lean is linked from {args.root.name}")
        return 0

    by_chapter = Counter(top_chapter(p) for p in missing)
    print(f"\nMissing from hierarchy: {len(missing)}")
    for chapter, count in by_chapter.most_common():
        print(f"  {chapter}: {count}")

    if args.list:
        print()
        for path in missing:
            print(path.relative_to(ROOT).as_posix())

    return 1


if __name__ == "__main__":
    raise SystemExit(main())
