#!/usr/bin/env python3
"""Split a Lean megafile into sequential under-500 hubs at namespace/section ends."""
from __future__ import annotations

import argparse
import re
from pathlib import Path


def safe_split_points(lines: list[str]) -> list[int]:
    """1-based line numbers that are safe to split AFTER (inclusive)."""
    pts: list[int] = []
    stack: list[tuple[str, str | None]] = []
    for i, l in enumerate(lines):
        s = l.strip()
        if s.startswith("namespace ") and not s.startswith("namespace DomainTheory"):
            stack.append(("ns", s.split()[1]))
        elif s.startswith("section"):
            name = s[7:].strip() or None
            stack.append(("sec", name))
        elif s.startswith("end"):
            rest = s[3:].strip()
            if rest.startswith("DomainTheory"):
                continue
            if stack:
                kind, name = stack[-1]
                if rest == "" or rest == name or (name and rest == name):
                    stack.pop()
                    if not stack:
                        pts.append(i + 1)
    return pts


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("src")
    ap.add_argument("--limit", type=int, default=480)
    ap.add_argument("--stem-prefix", default=None)
    args = ap.parse_args()
    src = Path(args.src)
    lines = src.read_text().splitlines(keepends=True)
    imps = [l.rstrip() for l in lines if l.startswith("public import ")]
    # body after first namespace DomainTheory
    ns = next(i for i, l in enumerate(lines) if l.startswith("namespace DomainTheory.NeighbourhoodSystems"))
    # include everything from first DT namespace; keep preamble imports from original
    header_lines = lines[: next(i for i, l in enumerate(lines) if l.startswith("@[expose]"))]
    # Find body start: after @[expose] public section and first namespace open
    body_start = ns
    # drop final end DomainTheory
    body_end = len(lines)
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].startswith("end DomainTheory.NeighbourhoodSystems"):
            body_end = i
            break
    body = lines[body_start:body_end]
    # remap split points relative to body: compute on full file then adjust
    pts = [p for p in safe_split_points(lines) if body_start < p <= body_end]
    # Convert to indices into `lines` (1-based pts are line numbers)
    pts = sorted(set(pts))
    print("safe points", pts[:20], "..." if len(pts) > 20 else "", "count", len(pts))

    limit = args.limit
    chunks: list[tuple[int, int]] = []
    start = body_start
    while start < body_end:
        target = start + limit
        # pick largest safe point in (start, min(target, body_end)]
        cand = [p for p in pts if start < p <= min(target, body_end)]
        if not cand:
            # force split at target or body_end
            end = min(target, body_end)
            # extend to next blank/end-ish
            while end < body_end and lines[end - 1].strip() and not lines[end - 1].startswith("end"):
                end += 1
                if end - start > limit + 80:
                    break
        else:
            end = max(cand)
        if end <= start:
            end = min(start + limit, body_end)
        chunks.append((start, end))
        start = end
    print("chunks", [(a + 1, b, b - a) for a, b in chunks])

    stem = args.stem_prefix or src.stem
    base = src.parent
    created: list[Path] = []
    prev_mod = None
    for i, (a, b) in enumerate(chunks):
        name = stem if i == 0 else f"{stem}_part{i}"
        dest = base / f"{name}.lean"
        chunk_imps = list(imps)
        if prev_mod:
            chunk_imps.append(f"public import {prev_mod}")
        # first chunk keeps original path = overwrite src
        body_txt = "".join(lines[a:b]).rstrip() + "\n"
        # ensure starts with namespace
        if not body_txt.lstrip().startswith("namespace DomainTheory"):
            body_txt = "namespace DomainTheory.NeighbourhoodSystems\nopen NeighborhoodSystem\n\n" + body_txt
        text = (
            "module\n\n"
            + "\n".join(dict.fromkeys(chunk_imps))
            + "\n\n@[expose] public section\n\n"
            + body_txt
            + "\nend DomainTheory.NeighbourhoodSystems\n"
        )
        dest.write_text(text)
        created.append(dest)
        prev_mod = f"DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.{dest.stem}"
        print("wrote", dest.name, len(text.splitlines()))

    # If first chunk is not src, we overwrote via name=stem when i==0 and dest==src
    # Update barrel for part files
    barrel = Path("/home/catskills/Desktop/DomainTheory/DomainTheory.lean")
    bt = barrel.read_text()
    parent_line = f"import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.{src.stem}\n"
    for dest in created[1:]:
        line = f"import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.{dest.stem}\n"
        if line not in bt and parent_line in bt:
            bt = bt.replace(parent_line, parent_line + line, 1)
    barrel.write_text(bt)


if __name__ == "__main__":
    main()
