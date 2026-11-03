#!/usr/bin/env python3
"""Move 1976_Appendix_A.english proofs into section .english files."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DT = ROOT / "DomainTheory" / "DataTypesAsLattices"
APP = DT / "1976_Appendix_A.english"

# Inclusive 1-based line ranges in 1976_Appendix_A.english (after migration source).
SLICES: list[tuple[str, int, int]] = [
    ("1976_Continuous_functions.english", 3, 4),
    ("Graph/1976_Theorem_1_2.english", 5, 9),
    ("FixedPoint/1976_Theorem_1_3.english", 11, 23),
    ("FixedPoint/1976_Theorem_1_4.english", 25, 39),
    ("Embedding/1976_Theorem_1_5.english", 41, 49),
    ("Embedding/1976_Theorem_1_6.english", 51, 59),
    ("Lambda/1976_The_language_LAMBDA.english", 64, 67),
    ("Lambda/1976_The_language_LAMBDA.english", 135, 179),
    ("Lambda/theorem_2_1.english", 68, 82),
    ("Lambda/1976_Theorem_2_2.english", 84, 102),
    ("Lambda/1976_Theorem_2_3.english", 104, 108),
    ("Lambda/1976_Theorem_2_4.english", 110, 114),
    ("Lambda/1976_Theorem_2_5.english", 116, 133),
    ("Computability/1976_Definability.english", 181, 197),
    ("Enumeration/theorem_3_1.english", 212, 212),
    ("Enumeration/1976_Theorem_3_2.english", 199, 214),
    ("Enumeration/1976_Theorem_3_5.english", 216, 255),
    ("Enumeration/1976_Theorem_3_6.english", 257, 263),
    ("Enumeration/1976_Theorem_3_7.english", 265, 280),
    ("Retracts/1976_Retracts_and_data_types.english", 282, 283),
    ("Retracts/1976_Theorem_4_1.english", 284, 324),
    ("Retracts/theorem_4_2.english", 326, 330),
    ("Retracts/1976_Theorem_4_3.english", 332, 345),
    ("Retracts/1976_Theorem_4_5.english", 332, 345),
    ("Retracts/1976_Theorem_4_6.english", 346, 346),
]


def append_block(path: Path, block: str) -> None:
    block = block.strip()
    if not block:
        return
    if path.is_file() and block in path.read_text(encoding="utf-8"):
        return
    text = path.read_text(encoding="utf-8") if path.is_file() else ""
    text = text.rstrip() + "\n\n" + block + "\n"
    path.write_text(text, encoding="utf-8")


def main() -> None:
    lines = APP.read_text(encoding="utf-8").splitlines()
    for rel, start, end in SLICES:
        chunk = "\n".join(lines[start - 1 : end]).strip()
        append_block(DT / rel, chunk)

    emb = DT / "Embedding/1976_Theorem_1_6.english"
    if emb.is_file():
        t = emb.read_text(encoding="utf-8")
        t = t.replace(
            "In order to make the plan of the work clearer, the proofs of the theorems have been placed in an Appendix when they are more than simple exercises.",
            "",
        )
        emb.write_text(re.sub(r"\n{3,}", "\n\n", t).rstrip() + "\n", encoding="utf-8")

    APP.unlink(missing_ok=True)
    (DT / "1976_Appendix_A.md").unlink(missing_ok=True)
    print("Appendix A proofs migrated; appendix note removed.")


if __name__ == "__main__":
    main()
