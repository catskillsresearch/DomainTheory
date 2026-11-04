#!/usr/bin/env python3
"""Reslice sources/1976_DataTypes.md into .english files and wire @imports on hub notes.

Preserves existing @import \"*.lean\" blocks on each note.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DT = ROOT / "DomainTheory" / "DataTypesAsLattices"
SOURCE = ROOT / "sources" / "1976_DataTypes.md"

LEAN_IMPORT_RE = re.compile(r'^@import\s+"([^"]+\.lean)"', re.MULTILINE)
ENGLISH_IMPORT_RE = re.compile(r'^@import\s+"([^"]+\.english)"', re.MULTILINE)
H1_RE = re.compile(r"^#\s+(.+)$", re.MULTILINE)

# (md path relative to DT, english path relative to md's parent or absolute to DT)
# english None => md.stem + .english beside md
SLICE_NOTES: list[tuple[str, str | None]] = [
    ("1976_Introduction.md", "1976_Introduction.english"),
    ("Pomega/1976_Pomega.md", None),
    ("1976_Introduction_remarks.md", None),
    (
        "1976_Continuous_functions_Introduction.md",
        "1976_Continuous_functions.english",
    ),
    ("Pomega/1976_e_definition.md", None),
    ("Pomega/1976_e_primrec.md", None),
    ("Pomega/1976_e_density.md", None),
    ("1976_Definition_basis.md", "1976_Definition_basis.english"),
    ("1976_Definition_continuous.md", "1976_Definition_continuous.english"),
    ("Continuous/1976_Theorem_1_1.md", None),
    ("Pomega/1976_pair.md", None),
    ("1976_Definition_graph.md", "1976_Definition_graph.english"),
    ("Graph/1976_Theorem_1_2.md", None),
    ("FixedPoint/1976_Theorem_1_3.md", None),
    ("FixedPoint/1976_Iteration_from_bot.md", None),
    ("FixedPoint/1976_Theorem_1_4.md", None),
    ("Embedding/1976_Theorem_1_5.md", None),
    ("Embedding/1976_Theorem_1_6.md", None),
    ("Lambda/1976_Computability_and_definability.md", None),
    ("Lambda/1976_Meaning.md", None),
    ("Lambda/1976_The_language_LAMBDA.md", None),
    ("Lambda/1976_Theorem_2_1.md", None),
    ("Lambda/1976_Theorem_2_2.md", None),
    ("Lambda/1976_Theorem_2_3.md", None),
    ("Lambda/1976_Theorem_2_4.md", None),
    ("Lambda/1976_Combinator_Y.md", None),
    ("Lambda/1976_Theorem_2_5.md", None),
    ("Lambda/1976_Graph_model.md", None),
    ("Lambda/1976_Elementary_definitions.md", None),
    ("Lambda/1976_Sequences.md", None),
    ("Lambda/1976_Distributive_functions.md", None),
    ("Lambda/1976_The_definability_theorem.md", None),
    ("Lambda/1976_Primitive_recursion.md", None),
    ("Lambda/1976_Definition_computable.md", "1976_Definition_computable.english"),
    ("Computability/1976_IsRE.md", "1976_IsRE.english"),
    ("Computability/1976_Finite_subsets.md", "1976_Finite_subsets.english"),
    ("Computability/1976_Pairing_terms.md", "1976_Pairing_terms.english"),
    ("Computability/1976_Constant_graph.md", "1976_Constant_graph.english"),
    ("Computability/1976_Code_enumerator.md", "1976_Code_enumerator.english"),
    ("Computability/1976_Definability.md", None),
    ("Lambda/1976_Law_of_Y.md", None),
    (
        "Enumeration/1976_Enumeration_and_degrees.md",
        "1976_Enumeration_and_degrees.english",
    ),
    ("Enumeration/1976_Theorem_3_1.md", None),
    ("Enumeration/1976_Theorem_3_2.md", None),
    ("Enumeration/1976_Theorem_3_3.md", None),
    ("Enumeration/1976_Theorem_3_4.md", None),
    ("Enumeration/1976_Theorem_3_5.md", None),
    ("Enumeration/1976_Theorem_3_6.md", None),
    ("Enumeration/1976_Theorem_3_7.md", None),
    (
        "Retracts/1976_Retracts_and_data_types.md",
        "1976_Retracts_and_data_types.english",
    ),
    ("Retracts/1976_Definition_retract.md", "1976_Definition_retract.english"),
    ("Retracts/1976_Theorem_4_1.md", None),
    ("Retracts/1976_Definition_membership.md", "1976_Definition_membership.english"),
    ("Retracts/1976_Definition_ordering.md", "1976_Definition_ordering.english"),
    ("Retracts/1976_Theorem_4_2.md", None),
    ("Retracts/1976_Theorem_4_3.md", None),
    ("Functionality/1976_Theorem_4_4.md", None),
    ("Retracts/1976_Theorem_4_5.md", None),
    ("Retracts/1976_Theorem_4_6.md", None),
    (
        "Closures/1976_Closure_operations_and_algebraic_lattices.md",
        "1976_Closure_operations_and_algebraic_lattices.english",
    ),
    ("Closures/1976_Definition_closure.md", "1976_Definition_closure.english"),
    ("Closures/1976_Theorem_5_1.md", None),
    ("Closures/1976_Theorem_5_2.md", None),
    ("Closures/1976_Theorem_5_3.md", None),
    ("Closures/1976_Theorem_5_4.md", None),
    ("Closures/1976_Theorem_5_5.md", None),
    ("Closures/1976_Theorem_5_6.md", None),
    (
        "Classification/1976_Subsets_and_their_classification.md",
        "1976_Subsets_and_their_classification.english",
    ),
    ("Classification/1976_Scott_classes.md", "Classification/1976_Scott_classes.english"),
    ("Classification/1976_Theorem_6_1.md", None),
    ("Classification/1976_Theorem_6_2.md", None),
    ("Classification/1976_Theorem_6_3.md", None),
    ("Classification/1976_Theorem_6_4.md", None),
    ("Classification/1976_Theorem_6_5.md", None),
    ("Classification/1976_Theorem_6_6.md", None),
    ("Classification/1976_Theorem_6_7.md", None),
    (
        "Functionality/1976_Total_functions_and_functionality.md",
        "1976_Total_functions_and_functionality.english",
    ),
    ("Functionality/1976_Definition_equivalence.md", "1976_Definition_equivalence.english"),
    ("Functionality/1976_Theorem_7_1.md", None),
    ("Functionality/1976_Theorem_7_2.md", None),
    ("Functionality/1976_Theorem_7_3.md", None),
    ("Functionality/1976_Theorem_7_4.md", None),
    ("1976_Appendix_B.md", "1976_Appendix_B.english"),
]

ANCHOR_OVERRIDE: dict[str, str] = {
    "1976_Introduction.md": "**Abstract.**",
    "Pomega/1976_Pomega.md": "The main innovation in this report",
    "1976_Introduction_remarks.md": "The model $\\mathbf{P}\\omega$ can be intuitively viewed",
    "1976_Continuous_functions_Introduction.md": "**1. Continuous functions.**",
    "Pomega/1976_e_definition.md": "To make the topology",
    "Pomega/1976_e_primrec.md": "the function $\\max(e_n)$ is (primitive) recursive",
    "Pomega/1976_e_density.md": "Topologically speaking",
    "Pomega/1976_pair.md": "To formulate the definition, we introduce a standard enumeration",
    "Lambda/1976_Computability_and_definability.md": "**2. Computability and definability.**",
    "1976_Appendix_B.md": "**Appendix B.",
}

# Section hubs with large Lean barrels — update .english only, not the .md wrapper.
LEAN_BARREL_HUBS = {
    "1976_Enumeration_and_degrees.md",
    "1976_Retracts_and_data_types.md",
    "1976_Closure_operations_and_algebraic_lattices.md",
    "1976_Subsets_and_their_classification.md",
    "1976_Total_functions_and_functionality.md",
}


@dataclass
class SliceTarget:
    md: Path
    english: Path
    start: int


def load_source(start_line: int) -> str:
    lines = SOURCE.read_text(encoding="utf-8").splitlines()
    return "\n".join(lines[start_line - 1 :])


def english_import_in_md(md: Path) -> Path | None:
    if not md.is_file():
        return None
    m = ENGLISH_IMPORT_RE.search(md.read_text(encoding="utf-8"))
    if not m:
        return None
    return md.parent / m.group(1)


def resolve_english(md: Path, eng_rel: str | None) -> Path:
    existing = english_import_in_md(md)
    if existing is not None:
        return existing
    if eng_rel is None:
        return md.with_suffix(".english")
    p = Path(eng_rel)
    if p.is_absolute():
        return p
    if eng_rel.startswith("1976_") and "/" not in eng_rel:
        return DT / eng_rel
    return md.parent / eng_rel


def find_start(source: str, md: Path, english: Path) -> int:
    rel = str(md.relative_to(DT))
    if rel in ANCHOR_OVERRIDE:
        idx = source.find(ANCHOR_OVERRIDE[rel])
        if idx >= 0:
            return idx
    if english.is_file():
        text = english.read_text(encoding="utf-8")
    elif md.is_file():
        text = md.read_text(encoding="utf-8")
        text = H1_RE.sub("", text, count=1)
        text = ENGLISH_IMPORT_RE.sub("", text)
        text = LEAN_IMPORT_RE.sub("", text)
    else:
        text = ""
    text = text.strip()
    if not text:
        raise SystemExit(f"no text to anchor {md}")
    for n in range(min(160, len(text)), 20, -1):
        chunk = text[:n]
        idx = source.find(chunk)
        if idx >= 0:
            return idx
    for line in text.splitlines():
        line = line.strip()
        if len(line) < 30:
            continue
        for n in range(min(len(line), 120), 30, -5):
            idx = source.find(line[:n])
            if idx >= 0:
                return idx
    raise SystemExit(f"anchor not found in source for {md} / {english}")


def preserve_prologue(md: Path) -> list[str]:
    """Editorial lines after the title, before the first .english import or Lean block."""
    if not md.is_file():
        return []
    lines = md.read_text(encoding="utf-8").splitlines()
    out: list[str] = []
    i = 1
    while i < len(lines) and not lines[i].strip():
        i += 1
    scott_inline = re.compile(
        r"^\*\*(DEFINITION\.|THEOREM|Abstract\.|Key words\.|Introduction\.)"
    )
    while i < len(lines):
        line = lines[i]
        if ENGLISH_IMPORT_RE.match(line):
            break
        if scott_inline.match(line):
            break
        if re.match(r"^\*\*\[.+\]\(.+\)\*\*\s*$", line):
            break
        if line.startswith('@import "') and line.endswith('.lean"'):
            break
        out.append(line)
        i += 1
    while out and not out[-1].strip():
        out.pop()
    return out


def preserve_lean_blocks(md: Path) -> list[str]:
    if not md.is_file():
        return []
    text = md.read_text(encoding="utf-8")
    lines = text.splitlines()
    out: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^\*\*\[(.+)\]\((.+)\)\*\*\s*$", line)
        if m and i + 1 < len(lines) and lines[i + 1].startswith('@import "'):
            out.append(line)
            out.append(lines[i + 1])
            i += 2
            if i < len(lines) and lines[i].strip() == "":
                out.append("")
                i += 1
            continue
        if line.startswith('@import "') and line.endswith('.lean"'):
            out.append(line)
            i += 1
            continue
        i += 1
    return out


def title_of(md: Path) -> str:
    if md.is_file():
        first = md.read_text(encoding="utf-8").splitlines()
        if first and first[0].startswith("# "):
            return first[0][2:].strip()
    return md.stem.replace("_", " ")


def write_note_md(md: Path, english: Path, extra_lines: list[str], lean_tail: list[str]) -> None:
    lines = [f"# {title_of(md)}", ""]
    lines.extend(extra_lines)
    if extra_lines and extra_lines[-1].strip():
        lines.append("")
    rel = os.path.relpath(english, md.parent).replace("\\", "/")
    lines.append(f'@import "{rel}" {{code_block=false}}')
    lines.append("")
    lines.extend(lean_tail)
    md.parent.mkdir(parents=True, exist_ok=True)
    md.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


PAGE_HEADER_LINE = re.compile(r"^\*\*DATA TYPES AS LATTICES\*\*\s*$", re.MULTILINE)


def strip_markdown_links_from_english(text: str) -> str:
    return re.sub(r"^- \[[^\]]+\]\([^)]+\)\s*$", "", text, flags=re.MULTILINE).strip()


def clean_english_slice(text: str) -> str:
    text = strip_markdown_links_from_english(text)
    text = PAGE_HEADER_LINE.sub("", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip() + "\n"


def patch_md_toc(md: Path, insert_after_h1: list[str]) -> None:
    if not md.is_file():
        return
    lean = preserve_lean_blocks(md)
    lines = [f"# {title_of(md)}", ""] + insert_after_h1 + lean
    md.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def update_hub_tocs() -> None:
    patch_md_toc(
        DT / "Continuous/1976_Continuous.md",
        [
            "- [Definition (basis)](../1976_Definition_basis.md)",
            "- [Definition (continuous)](../1976_Definition_continuous.md)",
            "- [Theorem 1.1](1976_Theorem_1_1.md)",
            "",
            '@import "Continuous.mermaid"',
            "",
        ],
    )
    patch_md_toc(
        DT / "Graph/1976_Graph.md",
        [
            '@import "Graph.mermaid"',
            "",
            "- [Definition (graph)](../1976_Definition_graph.md) ✓",
            "- [Theorem 1.2](1976_Theorem_1_2.md) ✓",
            "",
        ],
    )
    patch_md_toc(
        DT / "FixedPoint/1976_FixedPoint.md",
        [
            '@import "FixedPoint.mermaid"',
            "",
            "- [Theorem 1.3](1976_Theorem_1_3.md) ✓",
            "- [Iteration from $\\bot$ and **fix**](1976_Iteration_from_bot.md)",
            "- [Theorem 1.4](1976_Theorem_1_4.md)",
            "",
        ],
    )
    patch_md_toc(
        DT / "Embedding/1976_Embedding.md",
        [
            "- [Theorem 1.5](1976_Theorem_1_5.md)",
            "- [Theorem 1.6](1976_Theorem_1_6.md)",
            "",
            '@import "Embedding.mermaid"',
            "",
        ],
    )
    patch_md_toc(
        DT / "Lambda/1976_The_definability_theorem.md",
        [
            '@import "1976_The_definability_theorem.mermaid"',
            "",
            "- [Elementary definitions](1976_Elementary_definitions.md)",
            "- [Primitive recursion](1976_Primitive_recursion.md)",
            "- [Definition (computable)](1976_Definition_computable.md)",
            "- [R.e. subsets](../Computability/1976_IsRE.md)",
            "- [Finite subsets](../Computability/1976_Finite_subsets.md)",
            "- [Pairing terms](../Computability/1976_Pairing_terms.md)",
            "- [Constant graph](../Computability/1976_Constant_graph.md)",
            "- [Code enumerator](../Computability/1976_Code_enumerator.md)",
            "- [Theorem 2.6: Definability](../Computability/1976_Definability.md)",
            "",
            "",
        ],
    )

    hub = DT / "1976_DataTypes.md"
    hub.write_text(
        """# Data types as lattices

**Dependencies.** Each box is one section. The arrowhead is on the section that imports. The number is how many direct imports. An arrow already implied by a longer path is left out.

@import "1976_DataTypes.mermaid"

- [Introduction](1976_Introduction.md) [✓](1976_REVISION.md)
- [Continuous functions](1976_Continuous_functions.md)
- [Computability and definability](Lambda/1976_Computability_and_definability.md)
- [Enumeration and degrees](Enumeration/1976_Enumeration_and_degrees.md)
- [Retracts and data types](Retracts/1976_Retracts_and_data_types.md)
- [Closure operations and algebraic lattices](Closures/1976_Closure_operations_and_algebraic_lattices.md)
- [Subsets and their classification](Classification/1976_Subsets_and_their_classification.md)
- [Total functions and functionality](Functionality/1976_Total_functions_and_functionality.md)
- [Appendix B](1976_Appendix_B.md)
""",
        encoding="utf-8",
    )

    _write_revision_md()
    wire_section_child_tocs()


def wire_section_child_tocs() -> None:
    """Link definition/theorem notes from section hubs (after the section .english import)."""
    sections: list[tuple[str, list[str]]] = [
        (
            "Enumeration/1976_Enumeration_and_degrees.md",
            [
                "- [Theorem 3.1](1976_Theorem_3_1.md)",
                "- [Application](1976_Application.md)",
                "- [Numerals](1976_Numerals.md)",
                "- [Theorem 3.2](1976_Theorem_3_2.md)",
                "- [Theorem 3.3](1976_Theorem_3_3.md)",
                "- [Theorem 3.4](1976_Theorem_3_4.md)",
                "- [Theorem 3.5](1976_Theorem_3_5.md)",
                "- [Theorem 3.6](1976_Theorem_3_6.md)",
                "- [Theorem 3.7](1976_Theorem_3_7.md)",
            ],
        ),
        (
            "Retracts/1976_Retracts_and_data_types.md",
            [
                "- [Definition (retract)](1976_Definition_retract.md)",
                "- [Theorem 4.1](1976_Theorem_4_1.md)",
                "- [Definition (membership)](1976_Definition_membership.md)",
                "- [Definition (ordering)](1976_Definition_ordering.md)",
                "- [Theorem 4.2](1976_Theorem_4_2.md)",
                "- [Theorem 4.3](1976_Theorem_4_3.md)",
                "- [Theorem 4.4](../Functionality/1976_Theorem_4_4.md)",
                "- [Theorem 4.5](1976_Theorem_4_5.md)",
                "- [Theorem 4.6](1976_Theorem_4_6.md)",
            ],
        ),
        (
            "Closures/1976_Closure_operations_and_algebraic_lattices.md",
            [
                "- [Closure operation](1976_Definition_closure.md)",
                "- [Theorem 5.1 — the algebraic lattice theorem](1976_Theorem_5_1.md)",
                "- [Theorem 5.2 — the representation theorem](1976_Theorem_5_2.md)",
                "- [Theorem 5.3 — the function space theorem](1976_Theorem_5_3.md)",
                "- [Theorem 5.4 — the product and sum theorem](1976_Theorem_5_4.md)",
                "- [Theorem 5.5 — the universe theorem](1976_Theorem_5_5.md)",
                "- [Theorem 5.6 — the limit theorem](1976_Theorem_5_6.md)",
            ],
        ),
        (
            "Classification/1976_Subsets_and_their_classification.md",
            [
                "- [Scott classes](1976_Scott_classes.md)",
                "- [Theorem 6.1](1976_Theorem_6_1.md)",
                "- [Theorem 6.2](1976_Theorem_6_2.md)",
                "- [Theorem 6.3](1976_Theorem_6_3.md)",
                "- [Theorem 6.4](1976_Theorem_6_4.md)",
                "- [Theorem 6.5](1976_Theorem_6_5.md)",
                "- [Theorem 6.6](1976_Theorem_6_6.md)",
                "- [Theorem 6.7](1976_Theorem_6_7.md)",
            ],
        ),
        (
            "Functionality/1976_Total_functions_and_functionality.md",
            [
                "- [Pair elements](1976_Pair_elements.md)",
                "- [Restricted equivalence relations](1976_Definition_equivalence.md)",
                "- [Theorem 7.1](1976_Theorem_7_1.md)",
                "- [Theorem 7.2](1976_Theorem_7_2.md)",
                "- [Theorem 7.3](1976_Theorem_7_3.md)",
                "- [Theorem 7.4](1976_Theorem_7_4.md)",
            ],
        ),
    ]
    for rel, bullets in sections:
        md = DT / rel
        if not md.is_file():
            continue
        lines = md.read_text(encoding="utf-8").splitlines()
        out: list[str] = []
        inserted = False
        skip = set(bullets)
        for line in lines:
            if line in skip:
                continue
            out.append(line)
            if not inserted and ENGLISH_IMPORT_RE.match(line):
                out.append("")
                out.extend(bullets)
                out.append("")
                inserted = True
        if inserted:
            md.write_text("\n".join(out).rstrip() + "\n", encoding="utf-8")


def _write_revision_md() -> None:
    rev = DT / "1976_REVISION.md"
    if rev.is_file():
        rev.write_text(
            """# 1976 Data types as lattices — revision progress

Tracks the [revision ethos](../../README.md#revision): Mathlib-style library lemmas, Scott prose in `.english` notes, paper statements in `proposition_*` / `theorem_*` modules that assemble those tools.

**Complete** means the section’s notes (and Lean library/statement split where the section has formal content) match the revision ethos—not that later paper sections are finished.

| § | Section | Hub | Status |
| --- | --- | --- | --- |
| 0 | Introduction | [1976_Introduction.md](1976_Introduction.md) | **complete** (2026-11-01) |
| 1 | Continuous functions | [1976_Continuous_functions.md](1976_Continuous_functions.md) | pending |
| 2 | Computability and definability | [Lambda/1976_Computability_and_definability.md](Lambda/1976_Computability_and_definability.md) | pending |
| 3 | Enumeration and degrees | [Enumeration/1976_Enumeration_and_degrees.md](Enumeration/1976_Enumeration_and_degrees.md) | pending |
| 4 | Retracts and data types | [Retracts/1976_Retracts_and_data_types.md](Retracts/1976_Retracts_and_data_types.md) | pending |
| 5 | Closure operations and algebraic lattices | [Closures/1976_Closure_operations_and_algebraic_lattices.md](Closures/1976_Closure_operations_and_algebraic_lattices.md) | pending |
| 6 | Subsets and their classification | [Classification/1976_Subsets_and_their_classification.md](Classification/1976_Subsets_and_their_classification.md) | pending |
| 7 | Total functions and functionality | [Functionality/1976_Total_functions_and_functionality.md](Functionality/1976_Total_functions_and_functionality.md) | pending |

When a section is finished, set its status here and add the green **Revised** footer on that section’s hub and its note pages.
""",
            encoding="utf-8",
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-line", type=int, default=58)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    source = load_source(args.source_line)
    targets: list[SliceTarget] = []
    for md_rel, eng_rel in SLICE_NOTES:
        md = DT / md_rel
        eng = resolve_english(md, eng_rel)
        start = find_start(source, md, eng)
        targets.append(SliceTarget(md, eng, start))
    targets.sort(key=lambda t: t.start)

    for i, tgt in enumerate(targets):
        end = targets[i + 1].start if i + 1 < len(targets) else len(source)
        slice_text = source[tgt.start : end].strip() + "\n"
        slice_text = clean_english_slice(slice_text)
        if args.dry_run:
            print(f"write {tgt.english.relative_to(ROOT)} ({len(slice_text)} chars)")
            continue
        tgt.english.parent.mkdir(parents=True, exist_ok=True)
        tgt.english.write_text(slice_text, encoding="utf-8")

        if tgt.md.name.endswith("_Introduction.md") or tgt.md.name in {
            "1976_Continuous.md",
            "1976_Graph.md",
            "1976_FixedPoint.md",
            "1976_Embedding.md",
            "1976_Computability_and_definability.md",
        } or tgt.md.name in LEAN_BARREL_HUBS or (
            tgt.md.parent.name == "Pomega"
            and tgt.md.name not in {"1976_Pomega.md", "1976_e.md", "1976_pair.md"}
        ):
            continue
        lean = preserve_lean_blocks(tgt.md)
        prologue = preserve_prologue(tgt.md)
        extra = prologue + ([""] if prologue else [])
        write_note_md(tgt.md, tgt.english, extra, lean)

    if not args.dry_run:
        for name, title in (("1976_Appendix_B.md", "Appendix B"),):
            p = DT / name
            if not p.is_file():
                p.write_text(f"# {title}\n\n", encoding="utf-8")
            else:
                lines = p.read_text(encoding="utf-8").splitlines()
                if lines and lines[0].startswith("# "):
                    lines[0] = f"# {title}"
                    p.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")

        # Introduction note
        intro = DT / "1976_Introduction.md"
        memorial = "*To the Memory of Christopher Strachey, 1916–1975*\n\n"
        intro.write_text(
            "# Introduction\n\n"
            f"{memorial}"
            '@import "1976_Introduction.english" {code_block=false}\n\n'
            "- [Domain $\\mathbf{P}\\omega$](Pomega/1976_Pomega.md)\n"
            "- [Multiple-valued integers](1976_Introduction_remarks.md)\n",
            encoding="utf-8",
        )
        intro_eng = DT / "1976_Introduction.english"
        if intro_eng.is_file():
            body = intro_eng.read_text(encoding="utf-8")
            if memorial.strip() not in body:
                pass  # memorial stays in md only (extra)

        cf_intro = DT / "1976_Continuous_functions_Introduction.md"
        cf_intro.write_text(
            "# Introduction\n\n"
            '@import "1976_Continuous_functions.english" {code_block=false}\n\n'
            '<p style="color:#15803d;margin-top:1em;">✓ <strong>Revised</strong> '
            '(2026-11-01) — <a href="1976_REVISION.md">1976 revision progress</a></p>\n',
            encoding="utf-8",
        )

        lambda_hub = DT / "Lambda/1976_Computability_and_definability.md"
        if lambda_hub.is_file():
            patch_md_toc(
                lambda_hub,
                [
                    "**Historical note.** The language LAMBDA is Scott's. Plotkin and Rogers already used graphs, application, and conversion; the abstraction operation is what this section supplies.",
                    "",
                    '@import "1976_Computability_and_definability.mermaid"',
                    "",
                    "- [Minimal and maximal extension](1976_Extension.md) ✓",
                    "- [Meaning](1976_Meaning.md) ✓",
                    "- [The language LAMBDA](1976_The_language_LAMBDA.md) ✓",
                    "- [Theorem 2.1 — the continuity theorem](1976_Theorem_2_1.md)",
                    "- [Theorem 2.2 — the conversion theorem](1976_Theorem_2_2.md)",
                    "- [Theorem 2.3 — the reduction theorem](1976_Theorem_2_3.md)",
                    "- [Theorem 2.4 — the combinator theorem](1976_Theorem_2_4.md)",
                    "- [The combinator Y](1976_Combinator_Y.md)",
                    "- [Theorem 2.5 — the first recursion theorem](1976_Theorem_2_5.md)",
                    "- [The graph model](1976_Graph_model.md)",
                    "- [Sequences](1976_Sequences.md)",
                    "- [Distributive functions](1976_Distributive_functions.md)",
                    "- [The definability theorem](1976_The_definability_theorem.md)",
                    "- [A law of Y](1976_Law_of_Y.md)",
                    "",
                ],
            )

        update_hub_tocs()
        print(f"wrote {len(targets)} english slices from source line {args.source_line}")


if __name__ == "__main__":
    main()
