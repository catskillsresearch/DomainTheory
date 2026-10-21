#!/usr/bin/env python3
"""Remove `set_option linter.unusedSectionVars false` and trim `universe` names.

Keeps only universe parameters that appear in the file after the universe
declaration (in `Type u`, `.{u}`, `Sort u`, etc.). Does not edit `variable`
blocks; run `lake build` afterward to catch remaining linter warnings.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / "DomainTheory"

SET_OPTION = re.compile(r"^set_option linter\.unusedSectionVars false\s*\n", re.M)
UNIVERSE_LINE = re.compile(r"^(universe\s+)([a-zA-Z0-9_ ]+)(\s*)$", re.M)


def universe_used(name: str, body: str) -> bool:
    if not name:
        return False
    patterns = (
        rf"\.{re.escape(name)}\b",
        rf"\bType\s+\.{re.escape(name)}\b",
        rf"\bType\s+{re.escape(name)}\b",
        rf"\bSort\s+{re.escape(name)}\b",
        rf"\boutParam\s+{re.escape(name)}\b",
        rf"\b{re.escape(name)}\s*\+",
    )
    return any(re.search(p, body) for p in patterns)


def process_file(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    original = text
    text = SET_OPTION.sub("", text)
    if text.count("set_option linter.unusedSectionVars false") > 0:
        text = text.replace("set_option linter.unusedSectionVars false\n", "")
        text = text.replace("set_option linter.unusedSectionVars false", "")

    def repl_universe(match: re.Match[str]) -> str:
        prefix, names, suffix = match.group(1), match.group(2), match.group(3)
        start = match.end()
        body = text[start:]
        kept = [n for n in names.split() if universe_used(n, body)]
        if not kept:
            return ""
        return f"{prefix}{' '.join(kept)}{suffix}"

    text = UNIVERSE_LINE.sub(repl_universe, text)
    text = re.sub(r"\n{4,}", "\n\n\n", text)
    if text != original:
        path.write_text(text, encoding="utf-8")
        return True
    return False


def main() -> None:
    changed = 0
    for path in sorted(LIB.rglob("*.lean")):
        if process_file(path):
            changed += 1
    print(f"updated {changed} files under {LIB}")


if __name__ == "__main__":
    main()
