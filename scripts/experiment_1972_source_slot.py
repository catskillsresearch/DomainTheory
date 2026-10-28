#!/usr/bin/env python3
"""Experiment: align the 1972 chapter with sources/1972_ContinuousLattices.md.

A depth-first reading of the chapter concatenates ``.english`` slices back to
the source body. Every ``.lean`` file under ``ContinuousLattice`` is imported
from exactly one leaf. Barrel notes are a title, a Lean-import mermaid, and a
table of contents. Nothing outside this chapter is modified.
"""

from __future__ import annotations

import os
import re
import subprocess
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DT = ROOT / "DomainTheory"
CL = DT / "ContinuousLattice"
SOURCE = ROOT / "sources" / "1972_ContinuousLattices.md"

TOC_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?:[-*][ \t]+|\d+\.\s+)\[(?P<title>[^\]]*)\]\((?P<href>[^)]+\.md)\)[ \t]*$",
    re.MULTILINE,
)
LEAN_IMPORT_RE = re.compile(r'@import\s+"([^"]+\.lean)"')
ENGLISH_IMPORT_RE = re.compile(r'@import\s+"([^"]+\.english)"')
LEAN_MOD_IMPORT = re.compile(
    r"^(?:public\s+|private\s+|meta\s+)?import\s+(?:all\s+)?(\S+)\s*$"
)


class Leaf:
    def __init__(self, path: Path, title: str, anchor: str | None = None) -> None:
        self.path = path
        self.title = title
        self.anchor = anchor
        self.english: str | None = None
        self.leans: list[Path] = []


class Barrel:
    def __init__(self, path: Path, title: str, mermaid: str, children: list) -> None:
        self.path = path
        self.title = title
        self.mermaid = mermaid
        self.children = children
        self.english: str | None = None


def load_body() -> str:
    text = SOURCE.read_text(encoding="utf-8")
    return text[text.index("## ABSTRACT") :]


def P(*parts: str) -> Path:
    return CL.joinpath(*parts)


def spine_leaves() -> list[Leaf]:
    """Source anchors in reading order. Each slice runs until the next anchor."""
    rows = [
        ("## ABSTRACT", DT / "1972_Introduction.md", "Introduction"),
        ("**1. INJECTIVE SPACES.**", P("Injective/1972_T0_spaces.md"), "T0 spaces"),
        ("**1.1 Definition.**", P("Injective/1972_Definition_1_1.md"), "Definition 1.1: Injective Space"),
        ("**1.2 Proposition.**", P("Injective/1972_Proposition_1_2.md"), "Proposition 1.2"),
        ("**1.3 Proposition.**", P("Injective/1972_Proposition_1_3.md"), "Proposition 1.3"),
        ("**1.4 Proposition.**", P("Injective/1972_Proposition_1_4.md"), "Proposition 1.4"),
        ("**1.5 Proposition.**", P("Injective/1972_Proposition_1_5.md"), "Proposition 1.5"),
        ("**1.6 Corollary.**", P("Injective/1972_Corollary_1_6.md"), "Corollary 1.6"),
        ("**1.7 Corollary.**", P("Injective/1972_Corollary_1_7.md"), "Corollary 1.7"),
        (
            "As a result of these very elementary considerations",
            P("Injective/1972_Absolute_retracts.md"),
            "Absolute retracts",
        ),
        ("**2. CONTINUOUS LATTICES.**", P("Specialization/1972_Specialization.md"), "Specialization"),
        ("**2.1 Proposition.**", P("Specialization/1972_Proposition_2_1.md"), "Proposition 2.1"),
        ("Our main interest will lie", P("WayBelow/1972_WayBelow.md"), "Way-below relation"),
        ("**2.2 Proposition.**", P("WayBelow/1972_Proposition_2_2.md"), "Proposition 2.2"),
        ("**2.3 Definition.**", P("WayBelow/1972_ContinuousLattice.md"), "Definition 2.3"),
        ("**2.4 Proposition.**", P("ContinuousLattices/1972_Proposition_2_4.md"), "Proposition 2.4"),
        (
            "What is the idea of this definition?",
            P("ContinuousLattices/1972_Limits_and_convergence.md"),
            "Limits and convergence",
        ),
        ("**2.5 Proposition.**", P("ScottMaps/1972_Proposition_2_5.md"), "Proposition 2.5"),
        ("**2.6 Proposition.**", P("ScottMaps/1972_Proposition_2_6.md"), "Proposition 2.6"),
        ("**2.7 Proposition.**", P("ScottMaps/1972_Proposition_2_7.md"), "Proposition 2.7"),
        ("**2.8 Proposition.**", P("Constructions/1972_Proposition_2_8.md"), "Proposition 2.8"),
        ("**2.9 Proposition.**", P("Constructions/1972_Proposition_2_9.md"), "Proposition 2.9"),
        ("**2.10 Proposition.**", P("FunctionSpaces/1972_Proposition_2_10.md"), "Proposition 2.10"),
        ("**2.11 Proposition.**", P("Constructions/1972_Proposition_2_11.md"), "Proposition 2.11"),
        ("**2.12 Theorem.**", P("ContinuousLattices/1972_Theorem_2_12.md"), "Theorem 2.12"),
        ("**Proof of 2.9**", P("Constructions/1972_Proof_of_2_9.md"), "Proof of 2.9"),
        (
            "**Proof of 2.10**",
            P("FunctionSpaces/1972_Proposition_2_10_revisited.md"),
            "Proof of 2.10",
        ),
        ("*Proof of 2.11*", P("Constructions/1972_Proof_of_2_11.md"), "Proof of 2.11"),
        (
            "The lattice approach to injective spaces",
            P("ContinuousLattices/1972_After_theorem_2_12.md"),
            "After Theorem 2.12",
        ),
        ("**3. FUNCTION SPACES.**", P("FunctionSpaces/1972_Definition_3_1.md"), "Definition 3.1: Function space"),
        ("**3.2 Proposition.**", P("FunctionSpaces/1972_Proposition_3_2.md"), "Proposition 3.2"),
        ("**3.3 Theorem.**", P("FunctionSpaces/1972_Theorem_3_3.md"), "Theorem 3.3"),
        ("**3.4 Corollary.**", P("FunctionSpaces/1972_Corollary_3_4.md"), "Corollary 3.4"),
        ("**3.5 Proposition.**", P("FunctionSpaces/1972_Proposition_3_5.md"), "Proposition 3.5"),
        (
            "What will be useful will be to return",
            P("FunctionSpaces/1972_Before_definition_3_6.md"),
            "Retractions and extensions",
        ),
        ("**3.6 Definition.**", P("FunctionSpaces/1972_Definition_3_6.md"), "Definition 3.6"),
        ("**3.7 Proposition.**", P("FunctionSpaces/1972_Proposition_3_7.md"), "Proposition 3.7"),
        ("**3.8 Proposition.**", P("Constructions/1972_Proposition_3_8.md"), "Proposition 3.8"),
        ("**3.9 Lemma.**", P("FunctionSpaces/1972_Lemma_3_9.md"), "Lemma 3.9"),
        ("**3.10 Proposition.**", P("FunctionSpaces/1972_Proposition_3_10.md"), "Proposition 3.10"),
        ("**3.11 Definition.**", P("FunctionSpaces/1972_Definition_3_11.md"), "Definition 3.11: Projection space"),
        ("**3.12 Proposition.**", P("FunctionSpaces/1972_Proposition_3_12.md"), "Proposition 3.12"),
        ("**3.13 Proposition.**", P("FunctionSpaces/1972_Proposition_3_13.md"), "Proposition 3.13"),
        ("**3.14 Proposition.**", P("FunctionSpaces/1972_Proposition_3_14.md"), "Proposition 3.14"),
        ("**4. INVERSE LIMITS.**", P("InverseLimits/1972_Inverse_limits.md"), "Inverse limits"),
        ("**4.1 Proposition.**", P("InverseLimits/1972_Proposition_4_1.md"), "Proposition 4.1"),
        ("**4.2 Proposition.**", P("InverseLimits/1972_Proposition_4_2.md"), "Proposition 4.2"),
        ("**4.3 Corollary.**", P("InverseLimits/1972_Corollary_4_3.md"), "Corollary 4.3"),
        ("**4.4 Theorem.**", P("FunctionSpaceTower/1972_theorem_4_4.md"), "Theorem 4.4"),
        ("**4.5 Lemma.**", P("InverseLimits/1972_Lemma_4_5.md"), "Lemma 4.5"),
        (
            "**Proof of 4.4 concluded:**",
            P("FunctionSpaceTower/1972_Proof_of_4_4.md"),
            "Proof of 4.4 concluded",
        ),
        (
            "We can explain the idea of this proof",
            P("InverseLimits/1972_Functorial_form.md"),
            "The functorial form",
        ),
        ("Since we have shown", P("InverseLimits/1972_Application.md"), "Application"),
        (
            "Suppose we were to start with the least",
            P("InverseLimits/1972_Two_projections.md"),
            "Two projections",
        ),
        (
            "The reader will have surely remarked",
            P("InverseLimits/1972_Embedding_every_space.md"),
            "Embedding every space",
        ),
        (
            "The idea of forming the limit space",
            P("InverseLimits/1972_Other_functors.md"),
            "Other functors",
        ),
        (
            "The space $V$ constructed",
            P("InverseLimits/1972_Subspaces_of_a_limit.md"),
            "Subspaces of a limit",
        ),
        ("*Correction*", P("MilnerCorrection/1972_Correction.md"), "Correction"),
    ]
    return [Leaf(path, title, anchor) for anchor, path, title in rows]


def assign_slices(body: str, leaves: list[Leaf]) -> None:
    positions: list[int] = []
    cursor = 0
    for leaf in leaves:
        assert leaf.anchor is not None
        idx = body.find(leaf.anchor, cursor)
        if idx < 0:
            raise SystemExit(f"anchor not found in order: {leaf.anchor!r}")
        positions.append(idx)
        cursor = idx + 1
    for i, leaf in enumerate(leaves):
        end = positions[i + 1] if i + 1 < len(positions) else len(body)
        leaf.english = body[positions[i] : end]
        if not leaf.english.strip():
            raise SystemExit(f"empty slice for {leaf.path}")


def L(rel: str, title: str | None = None) -> Leaf:
    path = P(rel)
    if title is None:
        if path.is_file():
            first = path.read_text(encoding="utf-8").splitlines()[0]
            title = first[2:].strip() if first.startswith("# ") else path.stem
        else:
            title = path.stem
    return Leaf(path, title, None)


def build_tree(spine: dict[Path, Leaf]) -> Barrel:
    def S(path: Path) -> Leaf:
        return spine[path]

    spec = Barrel(
        P("Specialization/1972_Specialization_order.md"),
        "Specialization",
        "Specialization.mermaid",
        [
            S(P("Specialization/1972_Specialization.md")),
            L("WayBelow/1972_ScottOpen.md"),
            S(P("Specialization/1972_Proposition_2_1.md")),
        ],
    )
    scott = Barrel(
        P("ScottMaps/1972_Scott_maps.md"),
        "Scott maps",
        "ScottMaps.mermaid",
        [
            S(P("ScottMaps/1972_Proposition_2_5.md")),
            S(P("ScottMaps/1972_Proposition_2_6.md")),
            S(P("ScottMaps/1972_Proposition_2_7.md")),
        ],
    )
    sec2 = Barrel(
        P("1972_2_Continuous_lattices.md"),
        "Continuous lattices",
        "1972_2_Continuous_lattices.mermaid",
        [
            spec,
            S(P("WayBelow/1972_WayBelow.md")),
            S(P("WayBelow/1972_Proposition_2_2.md")),
            S(P("WayBelow/1972_ContinuousLattice.md")),
            S(P("ContinuousLattices/1972_Proposition_2_4.md")),
            S(P("ContinuousLattices/1972_Limits_and_convergence.md")),
            scott,
            S(P("Constructions/1972_Proposition_2_8.md")),
            S(P("Constructions/1972_Proposition_2_9.md")),
            S(P("FunctionSpaces/1972_Proposition_2_10.md")),
            S(P("Constructions/1972_Proposition_2_11.md")),
            S(P("ContinuousLattices/1972_Theorem_2_12.md")),
            S(P("Constructions/1972_Proof_of_2_9.md")),
            S(P("FunctionSpaces/1972_Proposition_2_10_revisited.md")),
            S(P("Constructions/1972_Proof_of_2_11.md")),
            S(P("ContinuousLattices/1972_After_theorem_2_12.md")),
        ],
    )
    sec3 = Barrel(
        P("1972_3_Function_spaces.md"),
        "Function spaces",
        "1972_Function_spaces.mermaid",
        [
            S(P("FunctionSpaces/1972_Definition_3_1.md")),
            S(P("FunctionSpaces/1972_Proposition_3_2.md")),
            S(P("FunctionSpaces/1972_Theorem_3_3.md")),
            S(P("FunctionSpaces/1972_Corollary_3_4.md")),
            S(P("FunctionSpaces/1972_Proposition_3_5.md")),
            S(P("FunctionSpaces/1972_Before_definition_3_6.md")),
            S(P("FunctionSpaces/1972_Definition_3_6.md")),
            S(P("FunctionSpaces/1972_Proposition_3_7.md")),
            S(P("Constructions/1972_Proposition_3_8.md")),
            S(P("FunctionSpaces/1972_Lemma_3_9.md")),
            S(P("FunctionSpaces/1972_Proposition_3_10.md")),
            S(P("FunctionSpaces/1972_Definition_3_11.md")),
            S(P("FunctionSpaces/1972_Proposition_3_12.md")),
            S(P("FunctionSpaces/1972_Proposition_3_13.md")),
            S(P("FunctionSpaces/1972_Proposition_3_14.md")),
        ],
    )
    inverse_system = Barrel(
        P("InverseLimits/1972_Inverse_system.md"),
        "The inverse system",
        "1972_Inverse_system.mermaid",
        [L("InverseLimits/1972_Compatible.md"), L("InverseLimits/1972_InverseLimit.md")],
    )
    embeddings = Barrel(
        P("InverseLimits/1972_Embeddings_into_the_limit.md"),
        "Embeddings into the limit",
        "1972_Embeddings_into_the_limit.mermaid",
        [L("InverseLimits/1972_embInfFun.md"), L("InverseLimits/1972_embInf.md")],
    )
    limit_lattice = Barrel(
        P("InverseLimits/1972_Limit_lattice.md"),
        "The limit lattice",
        "1972_Limit_lattice.mermaid",
        [
            L("InverseLimits/1972_inverseLimitPartialOrder.md"),
            L("InverseLimits/1972_inverseLimitSInfCoe.md"),
            L("InverseLimits/1972_InfSet.md"),
            L("InverseLimits/1972_instCompleteLattice.md"),
            L("InverseLimits/1972_coe_sSup_of_directed.md"),
        ],
    )
    projection = Barrel(
        P("FunctionSpaceTower/1972_Function_space_projection.md"),
        "The projection on a function space",
        "1972_Function_space_projection.mermaid",
        [
            L("FunctionSpaceTower/1972_functionSpaceInclFun.md"),
            L("FunctionSpaceTower/1972_functionSpaceRetrFun.md"),
            L("FunctionSpaceTower/1972_functionSpaceProjection.md"),
        ],
    )
    inverse_proof = Barrel(
        P("FunctionSpaceTower/1972_Limit_function_space_inverse.md"),
        "Proof that the limit and its function space are inverse",
        "1972_Limit_function_space_inverse.mermaid",
        [
            L("FunctionSpaceTower/1972_iInfTerm.md"),
            L("FunctionSpaceTower/1972_embInfInf.md"),
            L("FunctionSpaceTower/1972_jInfTerm.md"),
            L("FunctionSpaceTower/1972_incl_projInf.md"),
            L("FunctionSpaceTower/1972_iInfTerm_monotone.md"),
            L("FunctionSpaceTower/1972_embInf_succ_iSup.md"),
            L("FunctionSpaceTower/1972_iSup₂_monotone_eq_diagonal.md"),
            L("FunctionSpaceTower/1972_conjMap_iSup.md"),
            L("FunctionSpaceTower/1972_conj_iInfTerm_eq.md"),
            L("FunctionSpaceTower/1972_towerProj_retr_conjMap_succ.md"),
            L("FunctionSpaceTower/1972_projInfInf.md"),
            L("FunctionSpaceTower/1972_embInfInf_projInfInf.md"),
        ],
    )
    tower = Barrel(
        P("FunctionSpaceTower/1972_Function_space_tower.md"),
        "The function space tower",
        "1972_Function_space_tower.mermaid",
        [
            L("FunctionSpaceTower/1972_Tower_of_lattices.md"),
            L("FunctionSpaceTower/1972_Conjugation.md"),
            projection,
            L("FunctionSpaceTower/1972_Tower_projections.md"),
            L("FunctionSpaceTower/1972_DInf.md"),
            L("FunctionSpaceTower/1972_DInfFn.md"),
            inverse_proof,
            L("FunctionSpaceTower/1972_scottTopology.md"),
            L("FunctionSpaceTower/1972_sourceTopology.md"),
            S(P("FunctionSpaceTower/1972_theorem_4_4.md")),
            S(P("InverseLimits/1972_Lemma_4_5.md")),
            S(P("FunctionSpaceTower/1972_Proof_of_4_4.md")),
        ],
    )
    sec4 = Barrel(
        P("1972_4_Inverse_limits.md"),
        "Inverse limits",
        "1972_4_Inverse_limits.mermaid",
        [
            S(P("InverseLimits/1972_Inverse_limits.md")),
            inverse_system,
            L("InverseLimits/1972_projLE.md"),
            L("InverseLimits/1972_projection.md"),
            L("InverseLimits/1972_Projections_from_the_limit.md"),
            L("InverseLimits/1972_Embeddings_along_the_tower.md"),
            L("InverseLimits/1972_Embedding_coordinates.md"),
            embeddings,
            L("InverseLimits/1972_Mediating_map.md"),
            L("InverseLimits/1972_inverseLimitLE.md"),
            L("InverseLimits/1972_inverseLimitLT.md"),
            limit_lattice,
            L("InverseLimits/1972_inverseLimitTopology.md"),
            L("InverseLimits/1972_inverseLimit.md"),
            S(P("InverseLimits/1972_Proposition_4_1.md")),
            S(P("InverseLimits/1972_Proposition_4_2.md")),
            S(P("InverseLimits/1972_Corollary_4_3.md")),
            tower,
            S(P("InverseLimits/1972_Functorial_form.md")),
            S(P("InverseLimits/1972_Application.md")),
            S(P("InverseLimits/1972_Two_projections.md")),
            S(P("InverseLimits/1972_Embedding_every_space.md")),
            S(P("InverseLimits/1972_Other_functors.md")),
            S(P("InverseLimits/1972_Subspaces_of_a_limit.md")),
        ],
    )
    injective = Barrel(
        P("Injective/1972_Injective_spaces.md"),
        "Injective spaces",
        "Injective.mermaid",
        [
            S(P("Injective/1972_Definition_1_1.md")),
            S(P("Injective/1972_Proposition_1_2.md")),
            S(P("Injective/1972_Proposition_1_3.md")),
            S(P("Injective/1972_Powers_of_O_are_injective.md")),
            S(P("Injective/1972_Proposition_1_4.md")),
            S(P("Injective/1972_Proposition_1_5.md")),
            S(P("Injective/1972_RetractSubspace.md")),
            S(P("Injective/1972_Corollary_1_6.md")),
            S(P("Injective/1972_Corollary_1_7.md")),
            S(P("Injective/1972_Absolute_retracts.md")),
        ],
    )
    return Barrel(
        DT / "1972_ContinuousLattices.md",
        "Continuous Lattices",
        "1972_ContinuousLattices.mermaid",
        [
            S(DT / "1972_Introduction.md"),
            injective,
            sec2,
            sec3,
            sec4,
            S(P("MilnerCorrection/1972_Correction.md")),
        ],
    )


SECTION_BANNERS = (
    "**1. INJECTIVE SPACES.** ",
    "**2. CONTINUOUS LATTICES.** ",
    "**3. FUNCTION SPACES.** ",
    "**4. INVERSE LIMITS.** ",
)


def strip_banner(text: str) -> str:
    for banner in SECTION_BANNERS:
        if text.startswith(banner):
            return text[len(banner) :]
    raise SystemExit(f"section banner missing: {text[:80]!r}")


def find_barrel(node: Leaf | Barrel, path: Path) -> Barrel:
    if isinstance(node, Barrel) and node.path.resolve() == path.resolve():
        return node
    if isinstance(node, Barrel):
        for child in node.children:
            if isinstance(child, Barrel):
                found = find_barrel(child, path)
                if found is not None:
                    return found
    return None  # type: ignore[return-value]


def place_section_heads(tree: Barrel, spine: dict[Path, Leaf]) -> None:
    """Lift each unnumbered section opening onto the section note and drop the banner."""
    injective = find_barrel(tree, P("Injective/1972_Injective_spaces.md"))
    t0 = spine[P("Injective/1972_T0_spaces.md").resolve()]
    injective.english = strip_banner(t0.english or "")
    t0.english = None
    injective.children = [c for c in injective.children if getattr(c, "path", None) != t0.path]

    sec2 = find_barrel(tree, P("1972_2_Continuous_lattices.md"))
    spec = spine[P("Specialization/1972_Specialization.md").resolve()]
    sec2.english = strip_banner(spec.english or "")
    spec.english = None

    sec3 = find_barrel(tree, P("1972_3_Function_spaces.md"))
    defin = spine[P("FunctionSpaces/1972_Definition_3_1.md").resolve()]
    marker = "**3.1 Definition.**"
    text = defin.english or ""
    idx = text.find(marker)
    if idx < 0:
        raise SystemExit("Definition 3.1 marker missing from the section 3 opening")
    sec3.english = strip_banner(text[:idx])
    defin.english = text[idx:]

    sec4 = find_barrel(tree, P("1972_4_Inverse_limits.md"))
    opening = spine[P("InverseLimits/1972_Inverse_limits.md").resolve()]
    sec4.english = strip_banner(opening.english or "")
    opening.english = None
    sec4.children = [c for c in sec4.children if getattr(c, "path", None) != opening.path]


def drop_banner_notes() -> None:
    for path in (
        P("Injective/1972_T0_spaces.md"),
        P("Injective/1972_T0_spaces.english"),
        P("InverseLimits/1972_Inverse_limits.md"),
        P("InverseLimits/1972_Inverse_limits.english"),
        P("Specialization/1972_Specialization.english"),
    ):
        if path.is_file():
            path.unlink()


def walk_nodes(node: Leaf | Barrel):
    yield node
    if isinstance(node, Barrel):
        for child in node.children:
            yield from walk_nodes(child)


def leaves_in_order(node: Leaf | Barrel) -> list[Leaf]:
    if isinstance(node, Leaf):
        return [node]
    out: list[Leaf] = []
    for child in node.children:
        out.extend(leaves_in_order(child))
    return out


def existing_title(path: Path, fallback: str) -> str:
    if path.is_file():
        first = path.read_text(encoding="utf-8").splitlines()
        if first and first[0].startswith("# "):
            return first[0][2:].strip()
    return fallback


def original_text(md: Path) -> str:
    """Pre-experiment note text, so a re-run still sees the original citations."""
    rel = md.relative_to(ROOT).as_posix()
    proc = subprocess.run(
        ["git", "show", f"HEAD:{rel}"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode == 0:
        return proc.stdout
    if md.is_file():
        return md.read_text(encoding="utf-8", errors="ignore")
    return ""


def old_lean_importers() -> dict[Path, list[Path]]:
    found: dict[Path, list[Path]] = defaultdict(list)
    mds = list(CL.rglob("*.md")) + [
        DT / "1972_Introduction.md",
        P("1972_2_Continuous_lattices.md"),
        P("1972_3_Function_spaces.md"),
        P("1972_4_Inverse_limits.md"),
        DT / "1972_ContinuousLattices.md",
    ]
    for md in mds:
        text = original_text(md)
        if not text:
            continue
        for m in LEAN_IMPORT_RE.finditer(text):
            target = (md.parent / m.group(1)).resolve()
            if target.is_file():
                found[target].append(md.resolve())
    return found


def choose_leaf(lean: Path, by_path: dict[Path, Leaf]) -> Leaf:
    rel = lean.relative_to(CL).as_posix()
    stem = lean.stem

    def leaf(path: Path) -> Leaf:
        return by_path[path.resolve()]

    if rel.startswith("Injective/"):
        if "t0_" in stem or "Embedding" in stem:
            return leaf(P("Injective/1972_Proposition_1_5.md"))
        if "corollary_1_7" in stem:
            return leaf(P("Injective/1972_Corollary_1_7.md"))
        if "corollary_1_6" in stem:
            return leaf(P("Injective/1972_Corollary_1_6.md"))
        if "1_4" in stem or "retract" in stem or "Retract" in stem:
            return leaf(P("Injective/1972_Proposition_1_4.md"))
        if "1_3" in stem or "u2epi" in stem:
            return leaf(P("Injective/1972_Proposition_1_3.md"))
        if "1_2" in stem or "sierpinski" in stem.lower():
            return leaf(P("Injective/1972_Proposition_1_2.md"))
        return leaf(P("Injective/1972_Definition_1_1.md"))
    if rel.startswith("Specialization/"):
        if "proposition_2_1" in stem or "2_1" in stem:
            return leaf(P("Specialization/1972_Proposition_2_1.md"))
        return leaf(P("Specialization/1972_Specialization.md"))
    if rel.startswith("WayBelow/"):
        if "ScottOpen" in stem or "scottOpen" in stem or stem == "ScottOpen":
            return leaf(P("WayBelow/1972_ScottOpen.md"))
        if "proposition_2_2" in stem or stem == "proposition_2_2":
            return leaf(P("WayBelow/1972_Proposition_2_2.md"))
        if stem in {"ContinuousLattice", "bot_wayBelow"} or "continuousLattice" in stem:
            return leaf(P("WayBelow/1972_ContinuousLattice.md"))
        return leaf(P("WayBelow/1972_WayBelow.md"))
    if rel.startswith("ScottMaps/"):
        if "2_6" in stem or "proposition_2_6" in stem:
            return leaf(P("ScottMaps/1972_Proposition_2_6.md"))
        if "2_7" in stem or "meet_" in stem:
            return leaf(P("ScottMaps/1972_Proposition_2_7.md"))
        return leaf(P("ScottMaps/1972_Proposition_2_5.md"))
    if rel.startswith("Constructions/"):
        if "3_8" in stem or "proposition_3_8" in stem:
            return leaf(P("Constructions/1972_Proposition_3_8.md"))
        if "scottExtend" in stem or "2_11" in stem:
            if stem == "proposition_2_11":
                return leaf(P("Constructions/1972_Proposition_2_11.md"))
            return leaf(P("Constructions/1972_Proof_of_2_11.md"))
        if "2_9" in stem or "sierpinskiPower" in stem or "product" in stem:
            if stem == "proposition_2_9":
                return leaf(P("Constructions/1972_Proposition_2_9.md"))
            return leaf(P("Constructions/1972_Proof_of_2_9.md"))
        if "2_8" in stem or "finite" in stem:
            return leaf(P("Constructions/1972_Proposition_2_8.md"))
        return leaf(P("Constructions/1972_Proof_of_2_11.md"))
    if rel.startswith("ContinuousLattices/"):
        if "proposition_2_4" in stem:
            return leaf(P("ContinuousLattices/1972_Proposition_2_4.md"))
        if "lemma_3_9" in stem:
            return leaf(P("FunctionSpaces/1972_Lemma_3_9.md"))
        return leaf(P("ContinuousLattices/1972_Theorem_2_12.md"))
    if rel.startswith("MilnerCorrection/"):
        return leaf(P("MilnerCorrection/1972_Correction.md"))
    if rel.startswith("FunctionSpaceTower/"):
        return leaf(P("FunctionSpaceTower/1972_theorem_4_4.md"))
    if rel.startswith("InverseLimits/"):
        return leaf(P("InverseLimits/1972_Proposition_4_1.md"))
    if rel.startswith("FunctionSpaces/"):
        if stem == "proposition_2_10":
            return leaf(P("FunctionSpaces/1972_Proposition_2_10.md"))
        if "proposition_2_10" in stem:
            return leaf(P("FunctionSpaces/1972_Proposition_2_10_revisited.md"))
        if stem.startswith("fix") or "3_14" in stem:
            return leaf(P("FunctionSpaces/1972_Proposition_3_14.md"))
        if "3_13" in stem or stem.startswith("con_") or stem.startswith("min"):
            return leaf(P("FunctionSpaces/1972_Proposition_3_13.md"))
        if "3_12" in stem:
            return leaf(P("FunctionSpaces/1972_Proposition_3_12.md"))
        if "lemma_3_9" in stem or "3_9" in stem:
            return leaf(P("FunctionSpaces/1972_Lemma_3_9.md"))
        if "scottSubspace" in stem or "3_8" in stem:
            return leaf(P("Constructions/1972_Proposition_3_8.md"))
        if "3_10" in stem:
            return leaf(P("FunctionSpaces/1972_Proposition_3_10.md"))
        if "3_7" in stem or stem.startswith(("incl_", "retr_", "converse")):
            return leaf(P("FunctionSpaces/1972_Proposition_3_7.md"))
        if stem.startswith("IsProjection") or stem.startswith("IsContinuousLattice"):
            return leaf(P("FunctionSpaces/1972_Definition_3_6.md"))
        if "lambda" in stem.lower() or "curry" in stem or "3_5" in stem:
            return leaf(P("FunctionSpaces/1972_Proposition_3_5.md"))
        if "3_4" in stem or "eval" in stem.lower():
            return leaf(P("FunctionSpaces/1972_Corollary_3_4.md"))
        if "3_2" in stem:
            return leaf(P("FunctionSpaces/1972_Proposition_3_2.md"))
        if stem in {"ScottMap", "const", "const_apply"} or stem.startswith("scott"):
            return leaf(P("FunctionSpaces/1972_Definition_3_1.md"))
        return leaf(P("FunctionSpaces/1972_Theorem_3_3.md"))
    raise SystemExit(f"no leaf for {rel}")


def assign_leans(by_path: dict[Path, Leaf], order: list[Leaf]) -> None:
    rank = {leaf.path.resolve(): i for i, leaf in enumerate(order)}
    claimed: dict[Path, Leaf] = {}
    for lean, importers in old_lean_importers().items():
        leaves = [by_path[md] for md in importers if md in by_path]
        if not leaves:
            continue
        stem = lean.stem

        def rank_key(leaf: Leaf) -> tuple[int, int]:
            name = leaf.path.stem
            if name == stem or name.endswith(stem):
                return (0, rank[leaf.path.resolve()])
            if leaf.anchor is not None:
                return (1, rank[leaf.path.resolve()])
            return (2, rank[leaf.path.resolve()])

        leaves.sort(key=rank_key)
        claimed[lean] = leaves[0]
    for lean in sorted(CL.rglob("*.lean")):
        leaf = claimed.get(lean.resolve())
        if leaf is None:
            leaf = choose_leaf(lean, by_path)
        leaf.leans.append(lean.resolve())
    # The second half of the 4.4 formalization is the calculation after Lemma 4.5.
    more = P("FunctionSpaceTower/theorem_4_4_more.lean").resolve()
    proof = by_path[P("FunctionSpaceTower/1972_Proof_of_4_4.md").resolve()]
    for leaf in by_path.values():
        if more in leaf.leans and leaf is not proof:
            leaf.leans.remove(more)
    if more not in proof.leans:
        proof.leans.append(more)


def rel_md(barrel: Barrel, child: Leaf | Barrel) -> str:
    return Path(os.path.relpath(child.path, barrel.path.parent)).as_posix()


def rel_lean(md: Path, lean: Path) -> str:
    return Path(os.path.relpath(lean, md.parent)).as_posix()


def repo_lean(lean: Path) -> str:
    return lean.relative_to(ROOT).as_posix()


def write_leaf(leaf: Leaf) -> None:
    lines = [f"# {leaf.title}", ""]
    if leaf.english is not None:
        eng = leaf.path.with_name(leaf.path.stem + ".english")
        eng.parent.mkdir(parents=True, exist_ok=True)
        eng.write_text(leaf.english, encoding="utf-8")
        lines.append(f'@import "{eng.name}" {{code_block=false}}')
        lines.append("")
    for lean in sorted(leaf.leans, key=lambda p: p.as_posix()):
        shown = repo_lean(lean)
        lines.append(f"**[{shown}]({rel_lean(leaf.path, lean)})**")
        lines.append("")
        lines.append(f'@import "{rel_lean(leaf.path, lean)}"')
        lines.append("")
    leaf.path.parent.mkdir(parents=True, exist_ok=True)
    text = "\n".join(lines).rstrip() + "\n"
    leaf.path.write_text(text, encoding="utf-8")


def write_barrel(barrel: Barrel, numbered: bool) -> None:
    lines = [f"# {barrel.title}", ""]
    if barrel.english is not None:
        eng = barrel.path.with_name(barrel.path.stem + ".english")
        eng.parent.mkdir(parents=True, exist_ok=True)
        eng.write_text(barrel.english, encoding="utf-8")
        lines.append(f'@import "{eng.name}" {{code_block=false}}')
        lines.append("")
    lines.extend([f'@import "{barrel.mermaid}"', ""])
    for i, child in enumerate(barrel.children):
        href = rel_md(barrel, child)
        if numbered:
            lines.append(f"{i}. [{child.title}]({href})")
        else:
            lines.append(f"- [{child.title}]({href})")
    lines.append("")
    barrel.path.parent.mkdir(parents=True, exist_ok=True)
    barrel.path.write_text("\n".join(lines), encoding="utf-8")


def module_of(path: Path) -> str:
    rel = path.relative_to(ROOT)
    return ".".join(rel.with_suffix("").parts)


def path_of_module(mod: str) -> Path | None:
    if not mod.startswith("DomainTheory."):
        return None
    p = ROOT / Path(*mod.split(".")).with_suffix(".lean")
    return p if p.is_file() else None


def direct_imports(path: Path) -> list[str]:
    out = []
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        m = LEAN_MOD_IMPORT.match(line.strip())
        if m:
            out.append(m.group(1))
    return out


def transitive_reduce(pairs: set[tuple[str, str]]) -> set[tuple[str, str]]:
    adj: dict[str, set[str]] = defaultdict(set)
    for a, b in pairs:
        adj[a].add(b)

    def reachable(src: str, dst: str) -> bool:
        seen = {src}
        stack = [x for x in adj[src] if x != dst]
        while stack:
            n = stack.pop()
            if n == dst:
                return True
            if n in seen:
                continue
            seen.add(n)
            stack.extend(adj[n])
        return False

    return {(u, v) for u, v in pairs if not reachable(u, v)}


def mermaid_id(label: str, used: set[str]) -> str:
    base = re.sub(r"[^A-Za-z0-9_]", "_", label)
    base = base.strip("_") or "N"
    if base[0].isdigit():
        base = "N_" + base
    cand = base
    i = 0
    while cand in used:
        i += 1
        cand = f"{base}_{i}"
    used.add(cand)
    return cand


def subtree_leaves(node: Leaf | Barrel) -> list[Leaf]:
    return leaves_in_order(node)


def write_mermaid(barrel: Barrel) -> None:
    if barrel.path.name in {
        "1972_ContinuousLattices.md",
        "1972_2_Continuous_lattices.md",
        "1972_3_Function_spaces.md",
        "1972_4_Inverse_limits.md",
    }:
        return
    leans: list[Path] = []
    for leaf in subtree_leaves(barrel):
        leans.extend(leaf.leans)
    # stable unique
    seen: set[Path] = set()
    ordered: list[Path] = []
    for lean in leans:
        if lean not in seen:
            seen.add(lean)
            ordered.append(lean)
    used: set[str] = set()
    nid: dict[Path, str] = {}
    labels: dict[str, str] = {}
    for lean in ordered:
        folder = lean.parent.name
        raw = f"{folder}_{lean.stem}"
        ident = mermaid_id(raw, used)
        nid[lean] = ident
        labels[ident] = lean.stem
    edges: dict[tuple[str, str], int] = defaultdict(int)
    for lean in ordered:
        dst = nid[lean]
        for mod in direct_imports(lean):
            src_path = path_of_module(mod)
            if src_path is None:
                continue
            src_path = src_path.resolve()
            if src_path not in nid or src_path == lean:
                continue
            edges[(nid[src_path], dst)] += 1
    kept = transitive_reduce(set(edges))
    lines = [
        "%% Lean files imported under this note.",
        "%% Arrowhead on the importer. The number is a direct-import count.",
        "%% An arrow already implied by a longer path is omitted.",
        "flowchart TB",
        "",
    ]
    for ident in sorted(labels, key=lambda i: (labels[i].lower(), i)):
        lines.append(f'  {ident}["{labels[ident]}"]')
    lines.append("")
    for src, dst in sorted(kept, key=lambda e: (labels[e[1]].lower(), labels[e[0]].lower())):
        lines.append(f'  {src} -->|"{edges[(src, dst)]}"| {dst}')
    lines.append("")
    out = barrel.path.parent / barrel.mermaid
    out.write_text("\n".join(lines), encoding="utf-8")


def blank_unused(tree_paths: set[Path]) -> None:
    candidates = list(CL.rglob("*.md"))
    candidates.append(DT / "1972_TBD_prose.md")
    for md in candidates:
        if md.resolve() in tree_paths:
            continue
        if not md.is_file():
            continue
        first = md.read_text(encoding="utf-8", errors="ignore").splitlines()
        title = first[0][2:].strip() if first and first[0].startswith("# ") else md.stem
        md.write_text(f"# {title}\n", encoding="utf-8")


def concatenated_english(root: Barrel) -> str:
    parts: list[str] = []

    def walk(node: Leaf | Barrel) -> None:
        if isinstance(node, Barrel) and node.english is not None:
            eng = node.path.with_name(node.path.stem + ".english")
            parts.append(eng.read_text(encoding="utf-8"))
        if isinstance(node, Leaf):
            if node.english is not None:
                eng = node.path.with_name(node.path.stem + ".english")
                parts.append(eng.read_text(encoding="utf-8"))
            return
        for child in node.children:
            walk(child)

    walk(root)
    return "".join(parts)


def main() -> None:
    body = load_body()
    spine_list = spine_leaves()
    assign_slices(body, spine_list)
    spine = {leaf.path.resolve(): leaf for leaf in spine_list}
    if len(spine) != len(spine_list):
        raise SystemExit("duplicate spine path")
    tree = build_tree(spine)
    order = leaves_in_order(tree)
    # every spine leaf is visited once
    seen_spine = [leaf.path.resolve() for leaf in order if leaf.anchor is not None]
    if seen_spine != [leaf.path.resolve() for leaf in spine_list]:
        raise SystemExit("spine visit order does not match source order")
    place_section_heads(tree, spine)
    order = leaves_in_order(tree)
    by_path = {leaf.path.resolve(): leaf for leaf in order}
    assign_leans(by_path, order)

    def prune(node: Leaf | Barrel) -> None:
        if isinstance(node, Leaf):
            return
        kept = []
        for child in node.children:
            prune(child)
            if isinstance(child, Leaf) and child.anchor is None and not child.leans:
                continue
            if isinstance(child, Barrel) and not child.children:
                continue
            kept.append(child)
        node.children = kept

    prune(tree)
    order = leaves_in_order(tree)
    all_lean = sorted(p.resolve() for p in CL.rglob("*.lean"))
    assigned = [lean for leaf in order for lean in leaf.leans]
    if sorted(assigned) != all_lean:
        missing = set(all_lean) - set(assigned)
        extra = [p for p in assigned if assigned.count(p) > 1]
        raise SystemExit(f"lean coverage missing={len(missing)} dupes={len(set(extra))}")
    for node in walk_nodes(tree):
        if isinstance(node, Leaf):
            write_leaf(node)
        else:
            numbered = node.path.name == "1972_ContinuousLattices.md"
            write_barrel(node, numbered=numbered)
            write_mermaid(node)
    tree_paths = {node.path.resolve() for node in walk_nodes(tree)}
    blank_unused(tree_paths)
    drop_banner_notes()
    expected = body
    for banner in SECTION_BANNERS:
        if banner not in expected:
            raise SystemExit(f"banner not in source: {banner}")
        expected = expected.replace(banner, "", 1)
    got = concatenated_english(tree)
    if got != expected:
        # show first mismatch
        n = next((i for i, (a, b) in enumerate(zip(got, expected)) if a != b), min(len(got), len(expected)))
        raise SystemExit(
            f"reading invariant failed at {n}: got {got[max(0,n-40):n+40]!r} "
            f"src {expected[max(0,n-40):n+40]!r} lens {len(got)} {len(expected)}"
        )
    print(f"source chars {len(body)}")
    print(f"leaves {len(order)}")
    print(f"lean files {len(all_lean)}")
    print(f"barrels {sum(1 for n in walk_nodes(tree) if isinstance(n, Barrel))}")


if __name__ == "__main__":
    main()
