#!/usr/bin/env python3
"""Delete named theorem/def/abbrev blocks from a Lean file.

Finds each declaration's proof/term end by indentation (not "next decl"),
so intervening `namespace`/`section`/`end` are preserved.

Usage:
  python3 scripts/delete_lean_decls.py FILE name1 name2 ...
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

DECL_START = re.compile(
    r"^(?:noncomputable\s+)?(theorem|def|abbrev|structure|inductive|class|instance)\s+"
    r"([A-Za-z][\w']*|«[^»]+»)"
)


def find_decl_line(lines: list[str], name: str) -> int | None:
    for i, line in enumerate(lines):
        m = DECL_START.match(line)
        if m and m.group(2) == name:
            return i
    return None


def doc_start(lines: list[str], decl_i: int) -> int:
    j = decl_i - 1
    while j >= 0 and lines[j].strip() == "":
        j -= 1
    if j < 0:
        return decl_i
    if "-/" in lines[j]:
        k = j
        while k >= 0 and "/--" not in lines[k]:
            k -= 1
        if k >= 0 and "/--" in lines[k]:
            return k
    return decl_i


def proof_end(lines: list[str], decl_i: int) -> int:
    """Return exclusive end index of the declaration body."""
    i = decl_i
    # Advance to the line containing `:=` (may be several lines of binders).
    while i < len(lines) and ":=" not in lines[i]:
        i += 1
        # binders / types are indented or continuation
        if i < len(lines) and lines[i] and not lines[i][0].isspace() and not lines[i].startswith(
            "    "
        ):
            # hit a top-level line without := — malformed; stop
            if DECL_START.match(lines[i]) or lines[i].startswith(
                ("end", "namespace ", "section", "/--")
            ):
                return i
    if i >= len(lines):
        return len(lines)
    line = lines[i]
    # `:= by` proof
    if re.search(r":=\s*by\b", line) or line.rstrip().endswith("by"):
        i += 1
        while i < len(lines):
            l = lines[i]
            if l.strip() == "":
                # peek: blank inside proof vs after
                j = i + 1
                while j < len(lines) and lines[j].strip() == "":
                    j += 1
                if j < len(lines) and (lines[j][0].isspace() if lines[j] else False):
                    i = j
                    continue
                return i
            if l[0].isspace():
                i += 1
                continue
            return i
        return i
    # term mode: `:= expr` possibly multi-line indented
    if ":=" in line:
        # same-line complete term (no trailing open)
        rest = line.split(":=", 1)[1].strip()
        i += 1
        if rest and not rest.endswith(("by", "where")):
            # may still have indented continuation
            while i < len(lines) and lines[i] and lines[i][0].isspace():
                i += 1
            return i
        if rest.endswith("where") or " where" in line:
            # structure where fields — indented until dedent
            while i < len(lines):
                l = lines[i]
                if l.strip() == "":
                    j = i + 1
                    while j < len(lines) and lines[j].strip() == "":
                        j += 1
                    if j < len(lines) and lines[j] and lines[j][0].isspace():
                        i = j
                        continue
                    return i
                if l[0].isspace():
                    i += 1
                    continue
                return i
            return i
        while i < len(lines) and lines[i] and lines[i][0].isspace():
            i += 1
        return i
    return i + 1


def expand_empty_section(lines: list[str], s: int, e: int) -> tuple[int, int]:
    i = s - 1
    while i >= 0 and lines[i].strip() == "":
        i -= 1
    if i >= 0 and (lines[i].strip() == "section" or lines[i].startswith("section ")):
        j = e
        while j < len(lines) and lines[j].strip() == "":
            j += 1
        if j < len(lines) and lines[j].strip() == "end":
            return i, j + 1
    return s, e


def main() -> int:
    if len(sys.argv) < 3:
        print("usage: delete_lean_decls.py FILE name...", file=sys.stderr)
        return 2
    path = Path(sys.argv[1])
    names = sys.argv[2:]
    lines = path.read_text(encoding="utf-8").splitlines(keepends=True)

    ranges: list[tuple[int, int, str]] = []
    for n in names:
        decl_i = find_decl_line(lines, n)
        if decl_i is None:
            print(f"missing: {n}", file=sys.stderr)
            return 1
        s = doc_start(lines, decl_i)
        e = proof_end(lines, decl_i)
        s, e = expand_empty_section(lines, s, e)
        ranges.append((s, e, n))
        print(f"plan {n}: lines {s + 1}-{e}")

    # overlap check on original indices
    ranges_sorted = sorted(ranges, key=lambda t: t[0])
    for a, b in zip(ranges_sorted, ranges_sorted[1:]):
        if a[1] > b[0]:
            print(f"OVERLAP: {a[2]} ({a[0]+1}-{a[1]}) vs {b[2]} ({b[0]+1}-{b[1]})", file=sys.stderr)
            return 1

    for s, e, n in sorted(ranges, key=lambda t: t[0], reverse=True):
        print(f"delete {n}: lines {s + 1}-{e}")
        del lines[s:e]

    text = "".join(lines)
    text = re.sub(r"\n{3,}", "\n\n", text)
    path.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
