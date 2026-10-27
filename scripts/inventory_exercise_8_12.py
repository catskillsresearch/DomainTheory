#!/usr/bin/env python3
"""Classify decls in domainIso812c.lean: API / multi-internal / use-once / dead.

Usage:
  python3 scripts/inventory_exercise_8_12.py
  python3 scripts/inventory_exercise_8_12.py --csv /path/to/out.csv
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = (
    ROOT
    / "DomainTheory/NeighbourhoodSystems/RetractsOfTheUniversalDomain/domainIso812c.lean"
)

# Seed whitelist from the whittle plan (kept even if classification is soft).
SEED_API = {
    "splitX812e",
    "«812e»",
    "B812e",
    "U_isComputableDiff",
    "isomorphic_812c",
    "isomorphic_812d",
    "effectivelyIsomorphic_812d",
    "effectiveIso812d",
    "domainIsoCode812d",
    "domainIso812c",
    "XPseq",
    "YPseq",
    "XPseqCode",
    "YPseqCode",
    "SplitSpec'",
    "V_isPositive",
    "V_diffClosed",
    "V_noMinimal",
    "U_union_UX_mem",
    "VunionRaw",
    "exercise_8_12",
    "U_isPositive",
    "U_diffClosed",
    "U_noMinimal",
}

DECL_RE = re.compile(
    r"(?m)^(?:noncomputable\s+)?(theorem|def|abbrev|structure|inductive|class|instance)\s+"
    r"([A-Za-z][\w']*|«[^»]+»)"
)


def search_pat(name: str) -> str:
    # Apostrophe names: trailing `\b` fails because `'` is non-word (no boundary before space).
    if name.startswith("«"):
        return re.escape(name)
    if name.endswith("'"):
        return rf"(?<![\w']){re.escape(name)}(?![\w'])"
    return rf"\b{re.escape(name)}\b"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--csv", type=Path, default=None)
    args = ap.parse_args()

    text = TARGET.read_text(encoding="utf-8")
    decls: list[tuple[str, str, int]] = []  # kind, name, line
    for m in DECL_RE.finditer(text):
        kind, name = m.group(1), m.group(2)
        line = text.count("\n", 0, m.start()) + 1
        decls.append((kind, name, line))

    # Deduplicate by name keeping first occurrence (namespace reopens may redefine? rare)
    seen: set[str] = set()
    unique: list[tuple[str, str, int]] = []
    for kind, name, line in decls:
        if name in seen:
            continue
        seen.add(name)
        unique.append((kind, name, line))

    lean_files = [
        p
        for p in (ROOT / "DomainTheory").rglob("*.lean")
        if p.resolve() != TARGET.resolve()
    ]
    # Cache file texts
    external_texts: list[tuple[Path, str]] = []
    for p in lean_files:
        try:
            external_texts.append((p, p.read_text(encoding="utf-8")))
        except OSError:
            continue

    rows: list[dict[str, object]] = []
    for kind, name, line in unique:
        pat = search_pat(name)
        internal = len(re.findall(pat, text))
        ext_files: list[str] = []
        for p, t in external_texts:
            if re.search(pat, t):
                ext_files.append(p.relative_to(ROOT).as_posix())
        ext_count = len(ext_files)
        seeded = name in SEED_API
        if ext_count > 0 or seeded:
            klass = "API"
        elif internal <= 1:
            klass = "dead"
        elif internal == 2:
            # declaration + one use
            klass = "use_once"
        else:
            klass = "multi_internal"
        rows.append(
            {
                "kind": kind,
                "name": name,
                "line": line,
                "internal_refs": internal,
                "external_files": ext_count,
                "class": klass,
                "seed_api": seeded,
                "external_sample": ";".join(ext_files[:5]),
            }
        )

    rows.sort(key=lambda r: (str(r["class"]), -int(r["internal_refs"]), str(r["name"])))

    by_class: dict[str, int] = defaultdict(int)
    for r in rows:
        by_class[str(r["class"])] += 1

    print(f"decls: {len(rows)}")
    for k, v in sorted(by_class.items()):
        print(f"  {k}: {v}")

    out = args.csv
    if out is None:
        store = Path("/run/user/1000/cursor_agent_stores/fd188026-3c63-415f-9a57-4de084273fb0/files")
        if store.is_dir():
            out = store / "exercise_8_12_inventory.csv"
        else:
            out = ROOT / ".build" / "exercise_8_12_inventory.csv"
            out.parent.mkdir(parents=True, exist_ok=True)

    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()) if rows else [])
        w.writeheader()
        w.writerows(rows)
    print(f"wrote {out}")

    print("\n--- dead (candidates) ---")
    for r in rows:
        if r["class"] == "dead":
            print(f"  L{r['line']} {r['kind']} {r['name']}")
    print("\n--- use_once (first 40) ---")
    n = 0
    for r in rows:
        if r["class"] == "use_once":
            print(f"  L{r['line']} {r['kind']} {r['name']} (refs={r['internal_refs']})")
            n += 1
            if n >= 40:
                print("  ...")
                break
    return 0


if __name__ == "__main__":
    sys.exit(main())
