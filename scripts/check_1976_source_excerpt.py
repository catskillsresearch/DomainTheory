#!/usr/bin/env python3
"""Verify the 1976 paper excerpt (sources/1976_DataTypes.md from line 58).

Concatenates slice `.english` files in source order (same reslicing as
sync_1976_source_excerpt.py) and checks that text is a subsequence of the
source. Also requires every slice file to appear in the hub note tree; hub
DFS order may differ from paper order (reported separately).
"""

from __future__ import annotations

import argparse
import re
import sys
import unicodedata
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DT = ROOT / "DomainTheory" / "DataTypesAsLattices"
SOURCE = ROOT / "sources" / "1976_DataTypes.md"
HUB = DT / "1976_DataTypes.md"

sys.path.insert(0, str(ROOT / "scripts"))
from sync_1976_source_excerpt import (  # noqa: E402
    SLICE_NOTES,
    find_start,
    load_source,
    resolve_english,
)
from compile_md_tree import (  # noqa: E402
    REVISED_FOOTER_RE,
    child_md_targets,
    strip_toc_bullets,
)

IMPORT_ENG = re.compile(r'^@import\s+"([^"]+\.english)"', re.MULTILINE)


def ordered_notes(md_path: Path) -> list[Path]:
    out: list[Path] = []
    seen: set[Path] = set()

    def walk(p: Path) -> None:
        r = p.resolve()
        if r in seen:
            return
        seen.add(r)
        out.append(r)
        raw = r.read_text(encoding="utf-8")
        for _i, _t, ch in child_md_targets(r, raw):
            walk(ch)

    walk(md_path.resolve())
    return out


def english_imports_in_order(hub: Path) -> list[Path]:
    paths: list[Path] = []
    for note in ordered_notes(hub):
        raw = REVISED_FOOTER_RE.sub("\n", note.read_text(encoding="utf-8"))
        ch = child_md_targets(note, raw)
        body = strip_toc_bullets(raw) if ch else raw
        for m in IMPORT_ENG.finditer(body):
            ep = (note.parent / m.group(1)).resolve()
            paths.append(ep)
    return paths


def compact(s: str) -> str:
    s = unicodedata.normalize("NFKC", s)
    s = re.sub(r"<!--.*?-->", "", s, flags=re.DOTALL)
    s = re.sub(r"\*\*DATA TYPES AS LATTICES\*\*", "", s)
    s = re.sub(r"^#+\s.*$", "", s, flags=re.MULTILINE)
    s = re.sub(r"^@import.*$", "", s, flags=re.MULTILINE)
    s = re.sub(r"\[([^\]]*)\]\([^)]+\)", r"\1", s)
    s = re.sub(r"\s+", "", s)
    return s.lower()


def is_subsequence(needle: str, haystack: str) -> bool:
    n, h = compact(needle), compact(haystack)
    i = 0
    for c in n:
        if c.isspace():
            continue
        j = h.find(c, i)
        if j < 0:
            return False
        i = j + 1
    return True


def first_gap(needle: str, haystack: str, window: int = 50) -> tuple[int, str] | None:
    n, h = compact(needle), compact(haystack)
    pos = 0
    raw_pos = 0
    while pos < len(n):
        piece = n[pos : pos + window]
        j = h.find(piece)
        if j < 0:
            return raw_pos, needle[raw_pos : raw_pos + 120]
        h = h[j + len(piece) :]
        pos += window
        raw_pos += window
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-line", type=int, default=58, help="1-based start line")
    args = parser.parse_args()

    if not SOURCE.is_file():
        print(f"missing source: {SOURCE}", file=sys.stderr)
        return 1
    if not HUB.is_file():
        print(f"missing hub: {HUB}", file=sys.stderr)
        return 1

    lines = SOURCE.read_text(encoding="utf-8").splitlines()
    source_body = "\n".join(lines[args.source_line - 1 :])

    eng_paths = english_imports_in_order(HUB)
    missing = [p for p in eng_paths if not p.is_file()]
    if missing:
        print(f"missing {len(missing)} .english files referenced from hub tree")
        for p in missing[:20]:
            print(f"  {p.relative_to(ROOT)}")
        return 1

    source_for_anchor = load_source(args.source_line)
    slice_paths: list[Path] = []
    for md_rel, eng_rel in SLICE_NOTES:
        md = DT / md_rel
        eng = resolve_english(md, eng_rel).resolve()
        slice_paths.append((find_start(source_for_anchor, md, eng), eng))
    slice_paths.sort(key=lambda t: t[0])
    slice_paths = [eng for _start, eng in slice_paths]

    slice_missing = [p for p in slice_paths if not p.is_file()]
    if slice_missing:
        print(f"missing {len(slice_missing)} slice .english files")
        for p in slice_missing[:20]:
            print(f"  {p.relative_to(ROOT)}")
        return 1

    hub_set = {p.resolve() for p in eng_paths}
    unreachable = [p for p in slice_paths if p not in hub_set]
    extra_hub = [p for p in eng_paths if p not in set(slice_paths)]

    concat_slices = "\n\n".join(p.read_text(encoding="utf-8") for p in slice_paths)
    ok_slices = is_subsequence(source_body, concat_slices)
    concat_hub = "\n\n".join(p.read_text(encoding="utf-8") for p in eng_paths)
    ok_hub = is_subsequence(source_body, concat_hub)

    print(f"Hub notes: {len(ordered_notes(HUB))}")
    print(f"English @imports (hub DFS): {len(eng_paths)}")
    print(f"Slice spine files: {len(slice_paths)}")
    print(f"Source chars (from L{args.source_line}): {len(source_body):,}")
    print(f"Slice concat chars: {len(concat_slices):,}")
    print(f"Paper-order subsequence: {'OK' if ok_slices else 'FAIL'}")
    print(f"Hub DFS subsequence: {'OK' if ok_hub else 'FAIL (expected if TOC ≠ paper order)'}")
    if unreachable:
        print(f"Slice files not reachable from hub: {len(unreachable)}")
        for p in unreachable[:10]:
            print(f"  {p.relative_to(ROOT)}")
    if extra_hub:
        print(f"Extra hub .english (editorial): {len(extra_hub)}")
        for p in extra_hub[:10]:
            print(f"  {p.relative_to(ROOT)}")

    if not ok_slices:
        gap = first_gap(source_body, concat_slices)
        if gap:
            off, snip = gap
            print(f"First slice gap ~source offset {off}: {snip!r}...")
        return 1
    if unreachable:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
