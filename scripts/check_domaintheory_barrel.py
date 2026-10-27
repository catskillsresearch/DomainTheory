#!/usr/bin/env python3
"""Fail unless DomainTheory.lean imports every .lean file under DomainTheory/."""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DT = ROOT / "DomainTheory"
BARREL = ROOT / "DomainTheory.lean"


def main() -> int:
    mods = {
        "DomainTheory." + str(p.relative_to(DT).with_suffix("")).replace("/", ".")
        for p in DT.rglob("*.lean")
        if p.is_file()
    }
    imported = {
        line.split()[-1]
        for line in BARREL.read_text().splitlines()
        if line.startswith("import ") or line.startswith("public import ")
    }
    missing = sorted(mods - imported)
    extra = sorted(m for m in imported if m.startswith("DomainTheory.") and m not in mods)
    if missing or extra:
        for m in missing:
            print(f"missing import: {m}", file=sys.stderr)
        for m in extra:
            print(f"stale import: {m}", file=sys.stderr)
        print(
            f"DomainTheory.lean barrel out of sync: {len(missing)} missing, {len(extra)} stale "
            f"(filesystem {len(mods)}, barrel {len(imported)})",
            file=sys.stderr,
        )
        return 1
    print(f"OK: DomainTheory.lean imports all {len(mods)} modules under DomainTheory/")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
