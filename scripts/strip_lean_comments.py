#!/usr/bin/env python3
"""Remove Lean line (``--``) and block (``/- -/``) comments from ``.lean`` files."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DIR = ROOT / "DomainTheory"


def strip_lean_comments(text: str) -> str:
    """Drop comments; preserve string literals (``"..."``)."""
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c == '"':
            out.append(c)
            i += 1
            while i < n:
                ch = text[i]
                out.append(ch)
                if ch == "\\" and i + 1 < n:
                    out.append(text[i + 1])
                    i += 2
                    continue
                if ch == '"':
                    i += 1
                    break
                i += 1
            continue
        if c == "-" and i + 1 < n and text[i + 1] == "-":
            i += 2
            while i < n and text[i] not in "\n\r":
                i += 1
            continue
        if c == "/" and i + 1 < n and text[i + 1] == "-":
            depth = 1
            i += 2
            while i < n and depth > 0:
                if i + 1 < n and text[i : i + 2] == "/-":
                    depth += 1
                    i += 2
                elif i + 1 < n and text[i : i + 2] == "-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        out.append(c)
        i += 1
    result = "".join(out)
    result = re.sub(r"[ \t]+\n", "\n", result)
    result = re.sub(r"\n{3,}", "\n\n", result)
    return result.rstrip() + "\n"


def process_file(path: Path, *, write: bool) -> bool:
    original = path.read_text(encoding="utf-8")
    stripped = strip_lean_comments(original)
    if stripped == original:
        return False
    if write:
        path.write_text(stripped, encoding="utf-8")
    return True


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "paths",
        nargs="*",
        type=Path,
        help=f"files or dirs (default: {DEFAULT_DIR.relative_to(ROOT)})",
    )
    ap.add_argument("--write", action="store_true", help="modify files in place")
    ap.add_argument("--check", action="store_true", help="exit 1 if any file would change")
    args = ap.parse_args()

    roots = args.paths if args.paths else [DEFAULT_DIR]
    files: list[Path] = []
    for root in roots:
        root = root if root.is_absolute() else ROOT / root
        if root.is_file() and root.suffix == ".lean":
            files.append(root)
        elif root.is_dir():
            files.extend(sorted(root.rglob("*.lean")))

    changed = 0
    for path in files:
        if process_file(path, write=args.write):
            changed += 1
            if not args.write and not args.check:
                print(f"would update {path.relative_to(ROOT)}")

    if args.check and changed:
        print(f"{changed} files differ", file=sys.stderr)
        return 1
    if args.write:
        print(f"updated {changed} of {len(files)} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
