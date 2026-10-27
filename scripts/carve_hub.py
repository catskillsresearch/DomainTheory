#!/usr/bin/env python3
"""Carve a contiguous line range from a Lean megafile into a new hub module."""
from __future__ import annotations

import argparse
from pathlib import Path


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("src")
    ap.add_argument("dest")
    ap.add_argument("--start", type=int, required=True, help="1-based inclusive start line")
    ap.add_argument("--end", type=int, required=True, help="1-based inclusive end line")
    ap.add_argument("--imports", nargs="*", default=[])
    ap.add_argument("--parent-import", default=None, help="Insert public import of dest after this import line substring")
    ap.add_argument("--barrel-after", default=None, help="Insert DomainTheory.lean import after this module path")
    args = ap.parse_args()

    src = Path(args.src)
    dest = Path(args.dest)
    lines = src.read_text().splitlines(keepends=True)
    start, end = args.start - 1, args.end  # end exclusive in slice
    body = "".join(lines[start:end])
    while body.startswith("\n"):
        body = body[1:]
    while body.endswith("\n\n"):
        body = body[:-1]

    imp_block = "\n".join(f"public import {i}" for i in args.imports)
    header = f"""module

{imp_block}

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
"""
    footer = "\nend DomainTheory.NeighbourhoodSystems\n"
    dest.write_text(header + "\n" + body + footer)
    print(f"wrote {dest} ({len((header + body + footer).splitlines())} lines)")

    new_src = lines[:start] + ["\n"] + lines[end:]
    text = "".join(new_src)
    mod = f"DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.{dest.stem}"
    pub = f"public import {mod}\n"
    if pub not in text and args.parent_import:
        needle = f"public import {args.parent_import}\n"
        if needle not in text:
            raise SystemExit(f"parent import not found: {args.parent_import}")
        text = text.replace(needle, needle + pub, 1)
    elif pub not in text:
        # default: after first public import
        idx = text.find("public import ")
        nl = text.find("\n", idx) + 1
        text = text[:nl] + pub + text[nl:]
    src.write_text(text)
    print(f"updated {src} ({len(text.splitlines())} lines)")

    if args.barrel_after:
        barrel = Path("/home/catskills/Desktop/DomainTheory/DomainTheory.lean")
        bt = barrel.read_text()
        line = f"import {mod}\n"
        if line not in bt:
            after = f"import {args.barrel_after}\n"
            bt = bt.replace(after, after + line, 1)
            barrel.write_text(bt)
            print("barrel updated")


if __name__ == "__main__":
    main()
