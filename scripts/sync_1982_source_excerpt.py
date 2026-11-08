#!/usr/bin/env python3
"""1:1 reslice sources/1982_InformationSystems.md into note .english files.

Rewrites reachable notes under DomainTheory/1982_InformationSystems.md:
- barrels: title + SVG placeholder import + TOC + Lean blocks at bottom
- leaves: title + .english import + Lean blocks at bottom
Hard-fails unless cleaned source equals the ordered concat of .english slices.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DT = ROOT / "DomainTheory"
SOURCE = ROOT / "sources" / "1982_InformationSystems.md"
HUB = DT / "1982_InformationSystems.md"

PAGE_MARKER = re.compile(r"^<!--\s*page\s+\d+\s*-->\s*$", re.MULTILINE)
LEAN_IMPORT_RE = re.compile(r'^@import\s+"([^"]+\.lean)"', re.MULTILINE)
ENGLISH_IMPORT_RE = re.compile(r'^@import\s+"([^"]+\.english)"', re.MULTILINE)
H1_RE = re.compile(r"^#\s+(.+)$", re.MULTILINE)
TOC_BULLET = re.compile(r"^- \[[^\]]+\]\([^)]+\)\s*$", re.MULTILINE)

# (md relative to DT, english relative to md parent or DT-rooted name, anchor)
# english None => md.stem + .english beside md
SliceSpec = tuple[str, str | None, str]

# Ordered paper slices. Anchor is searched in cleaned source; first slice uses "".
SLICE_NOTES: list[SliceSpec] = [
    (
        "1982_Introduction.md",
        "1982_Introduction.english",
        "",  # abstract + §1 from start of cleaned source
    ),
    (
        "InformationSystems/InformationSystems/Constructive/1982_Introduction.md",
        "1982_Introduction.english",
        "**2. Information systems.**",
    ),
    (
        "InformationSystems/InformationSystems/InfoSys/1982_Definition_2_1.md",
        "InfoSys.english",
        "**DEFINITION 2.1.**",
    ),
    (
        "InformationSystems/InformationSystems/1982_A_first_example.md",
        "1982_A_first_example.english",
        "**A first example.**",
    ),
    (
        "InformationSystems/InformationSystems/1982_A_second_example.md",
        "1982_A_second_example.english",
        "**A second example.**",
    ),
    (
        "InformationSystems/InformationSystems/1982_A_third_example.md",
        "1982_A_third_example.english",
        "**A third example.**",
    ),
    (
        "InformationSystems/InformationSystems/Definition22/1982_Definition_2_2.md",
        "1982_Definition_2_2.english",
        "**DEFINITION 2.2.**",
    ),
    (
        "InformationSystems/InformationSystems/Proposition23/1982_Proposition_2_3.md",
        "1982_Proposition_2_3.english",
        "**PROPOSITION 2.3.**",
    ),
    (
        "InformationSystems/ElementsOfASystem/1982_Introduction.md",
        "1982_Introduction.english",
        "**3. The elements of a system.**",
    ),
    (
        "InformationSystems/ElementsOfASystem/1982_Definition_3_1.md",
        "1982_Definition_3_1.english",
        "**DEFINITION 3.1.**",
    ),
    (
        "InformationSystems/ElementsOfASystem/1982_Remarks.md",
        "1982_Remarks.english",
        "*Remarks.*",
    ),
    (
        "InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/1982_Introduction.md",
        "1982_Introduction.english",
        "**4. Domains as lattices and as topological spaces.**",
    ),
    (
        "InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/1982_Factoid_4_1.md",
        "1982_Factoid_4_1.english",
        "*Lattice-theoretic considerations.*",
    ),
    (
        "InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/1982_Factoid_4_2.md",
        "1982_Factoid_4_2.english",
        "What about infs of subsets?",
    ),
    (
        "InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid43/1982_Factoid_4_3.md",
        "1982_Factoid_4_3.english",
        "What about suprema (or sups or joins)?",
    ),
    (
        "InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid44/1982_Factoid_4_4.md",
        "1982_Factoid_4_4.english",
        "There is, however, an important case",
    ),
    (
        "InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid45/1982_Factoid_4_5.md",
        "1982_Factoid_4_5.english",
        "As we have remarked several times, any consistent set",
    ),
    (
        "InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/Factoid46/1982_Factoid_4_6.md",
        "1982_Factoid_4_6.english",
        "*Topological considerations.*",
    ),
    (
        "InformationSystems/ApproximableMappingsBetweenDomains/Approximable/1982_Introduction.md",
        "1982_Introduction.english",
        "**5. Approximable mappings between domains.**",
    ),
    (
        "InformationSystems/ApproximableMappingsBetweenDomains/Approximable/1982_Definition_5_1.md",
        "1982_Definition_5_1.english",
        "**DEFINITION 5.1.**",
    ),
    (
        "InformationSystems/ApproximableMappingsBetweenDomains/Approximable/1982_Definition_5_2.md",
        "1982_Definition_5_2.english",
        "**DEFINITION 5.2.**",
    ),
    (
        "InformationSystems/ApproximableMappingsBetweenDomains/Proposition53/1982_Proposition_5_3.md",
        "1982_Proposition_5_3.english",
        "**PROPOSITION 5.3.**",
    ),
    (
        "InformationSystems/ApproximableMappingsBetweenDomains/Proposition54/1982_Proposition_5_4.md",
        "1982_Proposition_5_4.english",
        "**PROPOSITION 5.4.**",
    ),
    (
        "InformationSystems/ApproximableMappingsBetweenDomains/Proposition55/1982_Proposition_5_5.md",
        "1982_Proposition_5_5.english",
        "**PROPOSITION 5.5.**",
    ),
    (
        "InformationSystems/ApproximableMappingsBetweenDomains/Proposition56/1982_Proposition_5_6.md",
        "1982_Proposition_5_6.english",
        "**PROPOSITION 5.6.**",
    ),
    (
        "InformationSystems/ProductsAndSumsOfDomains/Sum/1982_Introduction.md",
        "1982_Introduction.english",
        "**6. Products and sums of domains.**",
    ),
    (
        "InformationSystems/ProductsAndSumsOfDomains/Sum/1982_Definition_6_1.md",
        "1982_Definition_6_1.english",
        "**DEFINITION 6.1.**",
    ),
    (
        "InformationSystems/ProductsAndSumsOfDomains/Proposition62/1982_Proposition_6_2.md",
        "1982_Proposition_6_2.english",
        "**PROPOSITION 6.2.**",
    ),
    (
        "InformationSystems/ProductsAndSumsOfDomains/Sum/1982_Definition_6_3.md",
        "1982_Definition_6_3.english",
        "**DEFINITION 6.3.**",
    ),
    (
        "InformationSystems/ProductsAndSumsOfDomains/Proposition64/1982_Proposition_6_4.md",
        "1982_Proposition_6_4.english",
        "**PROPOSITION 6.4.**",
    ),
    (
        "InformationSystems/FunctionSpaceAsADomain/1982_Introduction.md",
        "1982_Introduction.english",
        "**7. The function space as a domain.**",
    ),
    (
        "InformationSystems/FunctionSpaceAsADomain/1982_Definition_7_1.md",
        "1982_Definition_7_1.english",
        "**DEFINITION 7.1.**",
    ),
    (
        "InformationSystems/FunctionSpaceAsADomain/Theorem72/1982_Theorem_7_2.md",
        "1982_Theorem_7_2.english",
        "**THEOREM 7.2.**",
    ),
    (
        "InformationSystems/FunctionSpaceAsADomain/1982_Theorem_7_3.md",
        "1982_Theorem_7_3.english",
        "**THEOREM 7.3.**",
    ),
    (
        "InformationSystems/FunctionSpaceAsADomain/Proposition74/1982_Proposition_7_4.md",
        "1982_Proposition_7_4.english",
        "**PROPOSITION 7.4.**",
    ),
    (
        "InformationSystems/SomeDomainEquations/1982_Introduction.md",
        "1982_Introduction.english",
        "**8. Some domain equations.**",
    ),
    (
        "InformationSystems/SomeDomainEquations/Factoid81/1982_Factoid_8_1.md",
        "1982_Factoid_8_1.english",
        "*A domain of trees or S-expressions.*",
    ),
    (
        "InformationSystems/SomeDomainEquations/Factoid82/1982_Factoid_8_2.md",
        "1982_Factoid_8_2.english",
        r"*A domain for $\lambda$-claculus.*",
    ),
    (
        "InformationSystems/SomeDomainEquations/Factoid83/1982_Factoid_8_3.md",
        "1982_Factoid_8_3.english",
        "*A universal domain.*",
    ),
    (
        "InformationSystems/SomeDomainEquations/Factoid84/1982_Factoid_8_4.md",
        "1982_Factoid_8_4.english",
        "*A domain of domains.*",
    ),
]

# Barrel md -> (svg basename, toc bullets as markdown lines)
BARRELS: dict[str, tuple[str, list[str]]] = {
    "1982_InformationSystems.md": (
        "1982_InformationSystems.svg",
        [
            "- [Introduction](1982_Introduction.md)",
            "- [Information systems](InformationSystems/InformationSystems/Constructive/1982_Information_systems.md)",
            "- [The elements of a system](InformationSystems/ElementsOfASystem/1982_The_elements_of_a_system.md)",
            "- [Domains as lattices and as topological spaces](InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/1982_Domains_as_lattices_and_as_topological_spaces.md)",
            "- [Approximable mappings between domains](InformationSystems/ApproximableMappingsBetweenDomains/Approximable/1982_Approximable_mappings_between_domains.md)",
            "- [Products and sums of domains](InformationSystems/ProductsAndSumsOfDomains/Sum/1982_Products_and_sums_of_domains.md)",
            "- [The function space as a domain](InformationSystems/FunctionSpaceAsADomain/1982_The_function_space_as_a_domain.md)",
            "- [Some domain equations](InformationSystems/SomeDomainEquations/1982_Some_domain_equations.md)",
        ],
    ),
    "InformationSystems/InformationSystems/Constructive/1982_Information_systems.md": (
        "1982_Information_systems.svg",
        [
            "- [Introduction](1982_Introduction.md)",
            "- [Definition 2.1](../InfoSys/1982_Definition_2_1.md)",
            "- [Lower-bound entailment](../1982_lowerBoundEnt.md)",
            "- [A first example](../1982_A_first_example.md)",
            "- [Interval tokens](../1982_Token.md)",
            "- [Satisfaction](../1982_Sat.md)",
            "- [A second example](../1982_A_second_example.md)",
            "- [Partial-function tokens](../1982_PartialFunToken.md)",
            "- [Partial-function system](../1982_partialFunctionSystem.md)",
            "- [A third example](../1982_A_third_example.md)",
            "- [Definition 2.2](../Definition22/1982_Definition_2_2.md)",
            "- [Finite union](../1982_funion.md)",
            "- [Proposition 2.3](../Proposition23/1982_Proposition_2_3.md)",
        ],
    ),
    "InformationSystems/ElementsOfASystem/1982_The_elements_of_a_system.md": (
        "1982_The_elements_of_a_system.svg",
        [
            "- [Introduction](1982_Introduction.md)",
            "- [Definition 3.1](1982_Definition_3_1.md)",
            "- [Total elements](1982_Total_elements.md)",
            "- [Top element](1982_Top_element.md)",
            "- [Remarks](1982_Remarks.md)",
        ],
    ),
    "InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/1982_Domains_as_lattices_and_as_topological_spaces.md": (
        "1982_Domains_as_lattices_and_as_topological_spaces.svg",
        [
            "- [Introduction](1982_Introduction.md)",
            "- [Inf](1982_inf.md)",
            "- [Factoid 4.1: lattice / binary meets](1982_Factoid_4_1.md)",
            "- [FamilyInf](1982_familyInf.md)",
            "- [Factoid 4.2: family infs](1982_Factoid_4_2.md)",
            "- [Factoid 4.3: joins / conditional sups](Factoid43/1982_Factoid_4_3.md)",
            "- [Factoid 4.4: chains & directed sups](Factoid44/1982_Factoid_4_4.md)",
            "- [Factoid 4.5: finite approximants](Factoid45/1982_Factoid_4_5.md)",
            "- [Factoid 4.6: topology / Scott continuity](Factoid46/1982_Factoid_4_6.md)",
        ],
    ),
    "InformationSystems/ApproximableMappingsBetweenDomains/Approximable/1982_Approximable_mappings_between_domains.md": (
        "1982_Approximable_mappings_between_domains.svg",
        [
            "- [Introduction](1982_Introduction.md)",
            "- [Definition 5.1](1982_Definition_5_1.md)",
            "- [Definition 5.2](1982_Definition_5_2.md)",
            "- [Proposition 5.3](../Proposition53/1982_Proposition_5_3.md)",
            "- [Proposition 5.4](../Proposition54/1982_Proposition_5_4.md)",
            "- [Proposition 5.5](../Proposition55/1982_Proposition_5_5.md)",
            "- [Proposition 5.6](../Proposition56/1982_Proposition_5_6.md)",
        ],
    ),
    "InformationSystems/ProductsAndSumsOfDomains/Sum/1982_Products_and_sums_of_domains.md": (
        "1982_Products_and_sums_of_domains.svg",
        [
            "- [Introduction](1982_Introduction.md)",
            "- [Definition 6.1](1982_Definition_6_1.md)",
            "- [Proposition 6.2](../Proposition62/1982_Proposition_6_2.md)",
            "- [Definition 6.3](1982_Definition_6_3.md)",
            "- [Proposition 6.4](../Proposition64/1982_Proposition_6_4.md)",
        ],
    ),
    "InformationSystems/FunctionSpaceAsADomain/1982_The_function_space_as_a_domain.md": (
        "1982_The_function_space_as_a_domain.svg",
        [
            "- [Introduction](1982_Introduction.md)",
            "- [Definition 7.1](1982_Definition_7_1.md)",
            "- [Theorem 7.2](Theorem72/1982_Theorem_7_2.md)",
            "- [Theorem 7.3](1982_Theorem_7_3.md)",
            "- [Proposition 7.4](Proposition74/1982_Proposition_7_4.md)",
        ],
    ),
    "InformationSystems/SomeDomainEquations/1982_Some_domain_equations.md": (
        "1982_Some_domain_equations.svg",
        [
            "- [Introduction](1982_Introduction.md)",
            "- [Factoid 8.1](Factoid81/1982_Factoid_8_1.md)",
            "- [Factoid 8.2](Factoid82/1982_Factoid_8_2.md)",
            "- [Factoid 8.3](Factoid83/1982_Factoid_8_3.md)",
            "- [Factoid 8.4](Factoid84/1982_Factoid_8_4.md)",
        ],
    ),
}

INTRO_TITLES: dict[str, str] = {
    "1982_Introduction.md": "Introduction",
    "InformationSystems/InformationSystems/Constructive/1982_Introduction.md": "Introduction",
    "InformationSystems/ElementsOfASystem/1982_Introduction.md": "Introduction",
    "InformationSystems/DomainsAsLatticesAndAsTopologicalSpaces/1982_Introduction.md": "Introduction",
    "InformationSystems/ApproximableMappingsBetweenDomains/Approximable/1982_Introduction.md": "Introduction",
    "InformationSystems/ProductsAndSumsOfDomains/Sum/1982_Introduction.md": "Introduction",
    "InformationSystems/FunctionSpaceAsADomain/1982_Introduction.md": "Introduction",
    "InformationSystems/SomeDomainEquations/1982_Introduction.md": "Introduction",
}


@dataclass
class SliceTarget:
    md: Path
    english: Path
    start: int


def clean_source(raw: str) -> str:
    text = raw
    # Drop leading H1 if present
    if text.startswith("# "):
        text = text.split("\n", 1)[1]
        if text.startswith("\n"):
            text = text[1:]
    text = PAGE_MARKER.sub("", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip() + "\n"


def normalize_join(text: str) -> str:
    text = re.sub(r"[ \t]+\n", "\n", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip() + "\n"


def preserve_lean_blocks(md: Path) -> list[str]:
    """Keep ``**[path](file.lean)**`` + ``@import`` pairs (blank line allowed between)."""
    if not md.is_file():
        return []
    lines = md.read_text(encoding="utf-8").splitlines()
    out: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^\*\*\[(.+)\]\((.+)\)\*\*\s*$", line)
        if m:
            j = i + 1
            while j < len(lines) and lines[j].strip() == "":
                j += 1
            if j < len(lines) and lines[j].startswith('@import "') and lines[j].endswith('.lean"'):
                out.append(line)
                out.append("")
                out.append(lines[j])
                out.append("")
                i = j + 1
                continue
        if line.startswith('@import "') and line.endswith('.lean"'):
            out.append(line)
            out.append("")
            i += 1
            continue
        i += 1
    while out and not out[-1].strip():
        out.pop()
    return out


def lean_import_count(md: Path) -> int:
    if not md.is_file():
        return 0
    return len(LEAN_IMPORT_RE.findall(md.read_text(encoding="utf-8")))


def title_of(md: Path, rel: str | None = None) -> str:
    if rel and rel in INTRO_TITLES:
        return INTRO_TITLES[rel]
    if md.is_file():
        first = md.read_text(encoding="utf-8").splitlines()
        if first and first[0].startswith("# "):
            return first[0][2:].strip()
    stem = md.stem
    stem = re.sub(r"^1982_", "", stem)
    return stem.replace("_", " ")


def resolve_english(md: Path, eng_rel: str | None) -> Path:
    if eng_rel is None:
        return md.with_suffix(".english")
    p = Path(eng_rel)
    if "/" not in eng_rel:
        return md.parent / eng_rel
    return DT / eng_rel


def find_anchor(source: str, anchor: str, min_pos: int = 0) -> int:
    if not anchor:
        return 0
    idx = source.find(anchor, min_pos)
    if idx < 0:
        raise SystemExit(f"anchor not found after {min_pos}: {anchor!r}")
    return idx


def write_leaf(md: Path, english: Path, lean: list[str], rel: str) -> None:
    title = title_of(md, rel)
    lines = [f"# {title}", ""]
    eng_rel = os.path.relpath(english, md.parent).replace("\\", "/")
    lines.append(f'@import "{eng_rel}" {{code_block=false}}')
    lines.append("")
    if lean:
        lines.extend(lean)
    md.parent.mkdir(parents=True, exist_ok=True)
    md.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def write_barrel(md: Path, svg_name: str, toc: list[str], lean: list[str], rel: str) -> None:
    title = title_of(md, rel)
    lines = [f"# {title}", ""]
    lines.append(f'@import "{svg_name}" {{code_block=false}}')
    lines.append("")
    lines.extend(toc)
    lines.append("")
    if lean:
        lines.extend(lean)
    md.parent.mkdir(parents=True, exist_ok=True)
    md.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def assert_coverage(source: str, english_paths: list[Path]) -> None:
    parts: list[str] = []
    for p in english_paths:
        if not p.is_file():
            raise SystemExit(f"missing english slice: {p}")
        parts.append(p.read_text(encoding="utf-8").strip())
    got = normalize_join("\n\n".join(parts) + "\n")
    want = normalize_join(source)
    if got != want:
        # Find first difference for diagnostics
        for i, (a, b) in enumerate(zip(got, want)):
            if a != b:
                lo = max(0, i - 60)
                raise SystemExit(
                    "1:1 coverage failed at char "
                    f"{i}:\n--- got ---\n{got[lo:i+80]!r}\n--- want ---\n{want[lo:i+80]!r}"
                )
        if len(got) != len(want):
            raise SystemExit(
                f"1:1 coverage failed: len got={len(got)} want={len(want)}"
            )
        raise SystemExit("1:1 coverage failed (unknown)")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    raw = SOURCE.read_text(encoding="utf-8")
    source = clean_source(raw)

    # Capture lean tails before any rewrite
    lean_by_rel: dict[str, list[str]] = {}
    lean_counts: dict[str, int] = {}
    all_rels = {spec[0] for spec in SLICE_NOTES} | set(BARRELS)
    for rel in all_rels:
        md = DT / rel
        lean_by_rel[rel] = preserve_lean_blocks(md)
        lean_counts[rel] = lean_import_count(md)

    targets: list[SliceTarget] = []
    cursor = 0
    for md_rel, eng_rel, anchor in SLICE_NOTES:
        md = DT / md_rel
        eng = resolve_english(md, eng_rel)
        start = find_anchor(source, anchor, cursor if anchor else 0)
        if anchor and start < cursor:
            raise SystemExit(f"anchor went backwards: {anchor!r}")
        targets.append(SliceTarget(md, eng, start))
        cursor = start + (len(anchor) if anchor else 0)

    targets.sort(key=lambda t: t.start)
    # Ensure strictly increasing
    for i in range(1, len(targets)):
        if targets[i].start <= targets[i - 1].start:
            raise SystemExit(
                f"non-increasing anchors: {targets[i-1].md.name} -> {targets[i].md.name}"
            )

    english_order: list[Path] = []
    for i, tgt in enumerate(targets):
        end = targets[i + 1].start if i + 1 < len(targets) else len(source)
        slice_text = source[tgt.start : end].strip() + "\n"
        # Drop accidental TOC bullets if any leaked into source (none expected)
        slice_text = TOC_BULLET.sub("", slice_text)
        slice_text = normalize_join(slice_text)
        english_order.append(tgt.english)
        if args.dry_run:
            print(f"would write {tgt.english.relative_to(ROOT)} ({len(slice_text)} chars)")
            continue
        tgt.english.parent.mkdir(parents=True, exist_ok=True)
        tgt.english.write_text(slice_text, encoding="utf-8")

    if not args.dry_run:
        # Rewrite barrels
        for rel, (svg_name, toc) in BARRELS.items():
            md = DT / rel
            write_barrel(md, svg_name, toc, lean_by_rel.get(rel, []), rel)

        # Rewrite leaves / intros that have english
        barrel_set = set(BARRELS)
        for md_rel, eng_rel, _anchor in SLICE_NOTES:
            if md_rel in barrel_set:
                continue
            md = DT / md_rel
            eng = resolve_english(md, eng_rel)
            write_leaf(md, eng, lean_by_rel.get(md_rel, []), md_rel)

        assert_coverage(source, english_order)

        # Lean count stability for notes that existed before
        for rel, before in lean_counts.items():
            md = DT / rel
            after = lean_import_count(md)
            if after != before:
                raise SystemExit(
                    f"Lean @import count changed for {rel}: {before} -> {after}"
                )

        print(f"wrote {len(targets)} english slices; 1:1 coverage OK")
    else:
        # Dry-run coverage using would-be slices
        parts = []
        cursor_positions = [t.start for t in targets] + [len(source)]
        for i, tgt in enumerate(targets):
            chunk = normalize_join(source[cursor_positions[i] : cursor_positions[i + 1]])
            parts.append(chunk.strip())
        got = normalize_join("\n\n".join(parts) + "\n")
        want = normalize_join(source)
        if got != want:
            raise SystemExit("dry-run 1:1 coverage would fail")
        print(f"dry-run OK: {len(targets)} slices cover source")


if __name__ == "__main__":
    main()
