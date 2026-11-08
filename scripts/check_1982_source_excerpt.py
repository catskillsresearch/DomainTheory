#!/usr/bin/env python3
"""Verify 1982 Information Systems source ↔ .english 1:1 coverage and barrel shape."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DT = ROOT / "DomainTheory"
HUB = DT / "1982_InformationSystems.md"

sys.path.insert(0, str(ROOT / "scripts"))
from sync_1982_source_excerpt import (  # noqa: E402
    BARRELS,
    SLICE_NOTES,
    SOURCE,
    clean_source,
    lean_import_count,
    normalize_join,
    resolve_english,
)

ENGLISH_IMPORT = re.compile(r'^@import\s+"([^"]+\.english)"', re.MULTILINE)
SCOTTISH = re.compile(
    r"(?m)^(?:The |In |For |Let |We |This |An |A |If |Suppose |\*\*\d|\*\*DEFINITION|\*\*PROPOSITION|\*\*THEOREM)"
)


def main() -> None:
    source = clean_source(SOURCE.read_text(encoding="utf-8"))
    parts: list[str] = []
    for md_rel, eng_rel, _anchor in SLICE_NOTES:
        md = DT / md_rel
        eng = resolve_english(md, eng_rel)
        if not eng.is_file():
            raise SystemExit(f"missing {eng}")
        if not md.is_file():
            raise SystemExit(f"missing {md}")
        parts.append(eng.read_text(encoding="utf-8").strip())
        # Leaves/intros must import their english
        if md_rel not in BARRELS:
            text = md.read_text(encoding="utf-8")
            if not ENGLISH_IMPORT.search(text):
                raise SystemExit(f"{md_rel} missing .english @import")
            # Lean blocks must be after english import
            eng_pos = text.find('@import "')
            lean_pos = text.find(".lean")
            if lean_pos >= 0 and eng_pos > lean_pos:
                raise SystemExit(f"{md_rel}: Lean appears before english import")

    got = normalize_join("\n\n".join(parts) + "\n")
    want = normalize_join(source)
    if got != want:
        for i, (a, b) in enumerate(zip(got, want)):
            if a != b:
                lo = max(0, i - 40)
                raise SystemExit(
                    f"1:1 failed at {i}:\ngot {got[lo:i+60]!r}\nwant {want[lo:i+60]!r}"
                )
        raise SystemExit(f"1:1 failed lens got={len(got)} want={len(want)}")

    for rel, (svg_name, _toc) in BARRELS.items():
        md = DT / rel
        text = md.read_text(encoding="utf-8")
        if ENGLISH_IMPORT.search(text):
            raise SystemExit(f"barrel {rel} must not import .english")
        if f'@import "{svg_name}"' not in text:
            raise SystemExit(f"barrel {rel} missing SVG import {svg_name}")
        # No Scott prose paragraphs (heuristic: long non-structural lines)
        for ln in text.splitlines():
            if ln.startswith("#") or ln.startswith("@") or ln.startswith("- ") or ln.startswith("**["):
                continue
            if not ln.strip():
                continue
            if SCOTTISH.match(ln) or (len(ln) > 120 and not ln.startswith("**")):
                raise SystemExit(f"barrel {rel} still has prose: {ln[:80]!r}")
        svg = md.parent / svg_name
        if not svg.is_file():
            raise SystemExit(f"missing SVG {svg}")

    # Reachability: strict md walk from hub should hit every SLICE note + barrels
    link_re = re.compile(r"\[[^\]]*\]\(([^)]+\.md)\)")
    seen: set[Path] = set()
    stack = [HUB]
    while stack:
        p = stack.pop()
        rp = p.resolve()
        if rp in seen or not p.is_file():
            continue
        seen.add(rp)
        for m in link_re.finditer(p.read_text(encoding="utf-8")):
            stack.append((p.parent / m.group(1)).resolve())

    expected = { (DT / rel).resolve() for rel, _, _ in SLICE_NOTES }
    expected |= { (DT / rel).resolve() for rel in BARRELS }
    missing = sorted(expected - seen, key=str)
    if missing:
        raise SystemExit(
            "strict walk missed:\n" + "\n".join(str(p.relative_to(DT)) for p in missing)
        )

    print(
        f"OK: 1:1 coverage ({len(SLICE_NOTES)} slices), "
        f"{len(BARRELS)} barrels SVG-only, "
        f"strict walk reaches {len(seen)} notes"
    )


if __name__ == "__main__":
    main()
