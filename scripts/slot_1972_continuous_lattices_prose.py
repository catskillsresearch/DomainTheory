#!/usr/bin/env python3
"""Slot sources/1972_ContinuousLattices.md prose into chapter .english sidecars only.

Does not modify ``*.md`` notes (mermaid diagrams, Lean ``@import``s, and hub
TOCs stay as they are). Add ``@import "*.english"`` to a note by hand if needed.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "sources" / "1972_ContinuousLattices.md"
DT = ROOT / "DomainTheory"
TBD = DT / "1972_TBD_prose"

MARKER = re.compile(
    r"^(## ABSTRACT|## CONTENTS|## 0\. Introduction|\*\*\d+\."
    r"|\*\*Proof of \d+\."
    r"|\*Proof of \d+\."
    r"|\*\*Left projection|\*\*Right projection"
    r"|\*Correction)"
)


def load_body_lines() -> list[str]:
    lines = SOURCE.read_text(encoding="utf-8").splitlines()
    start = 0
    for i, line in enumerate(lines):
        if line.strip() == "## ABSTRACT":
            start = i
            break
    out = lines[start:]
    return [ln for ln in out if ln not in ("# CONTINUOUS LATTICES", "BY", "Dana Scott", "# Transcription (LLM vision OCR)")]


def segment_key(first_line: str) -> str:
    s = first_line.strip()
    if s.startswith("## ABSTRACT"):
        return "abstract"
    if s.startswith("## CONTENTS"):
        return "contents"
    if s.startswith("## 0."):
        return "sec0"
    m = re.match(r"\*\*(\d+\.\d+)\s+(Definition|Proposition|Corollary|Theorem)\.", s)
    if m:
        return m.group(1)
    m = re.match(r"\*\*(\d+)\.\s+([A-Z][A-Z\s]+)\.\*\*", s)
    if m:
        return f"sec{m.group(1)}"
    m = re.match(r"\*\*Proof of (\d+\.\d+)", s)
    if m:
        return f"proof_{m.group(1)}"
    m = re.match(r"\*Proof of (\d+\.\d+)", s)
    if m:
        return f"proof_{m.group(1)}"
    if s.startswith("*Correction"):
        return "correction"
    if "Left projection" in s:
        return "sec4_projections_figure"
    if "Right projection" in s:
        return "sec4_projections_figure"
    slug = re.sub(r"[^a-z0-9]+", "_", s[:60].lower()).strip("_") or "fragment"
    return f"frag_{slug}"


def path_for_key(key: str) -> Path:
    m = {
        "abstract": DT / "1972_Introduction.english",
        "contents": TBD / "contents.english",
        "sec0": DT / "1972_Introduction.english",
        "sec1": DT / "ContinuousLattice/Injective/1972_T0_spaces.english",
        "1.1": DT / "ContinuousLattice/Injective/InjectiveSpace.english",
        "1.2": DT / "ContinuousLattice/Injective/1972_Proposition_1_2.english",
        "1.3": DT / "ContinuousLattice/Injective/1972_Proposition_1_3.english",
        "1.4": DT / "ContinuousLattice/Injective/1972_Proposition_1_4.english",
        "1.5": DT / "ContinuousLattice/Injective/1972_Proposition_1_5.english",
        "1.6": DT / "ContinuousLattice/Injective/corollary_1_6.english",
        "1.7": DT / "ContinuousLattice/Injective/corollary_1_7.english",
        "sec2": DT / "ContinuousLattice/Specialization/1972_Specialization.english",
        "2.1": DT / "ContinuousLattice/Specialization/1972_Proposition_2_1.english",
        "2.2": DT / "ContinuousLattice/WayBelow/1972_Proposition_2_2.english",
        "2.3": DT / "ContinuousLattice/WayBelow/1972_ContinuousLattice.english",
        "2.4": DT / "ContinuousLattice/ContinuousLattices/1972_Proposition_2_4.english",
        "2.5": DT / "ContinuousLattice/ScottMaps/1972_Proposition_2_5.english",
        "2.6": DT / "ContinuousLattice/ScottMaps/proposition_2_6.english",
        "2.7": DT / "ContinuousLattice/ScottMaps/1972_Proposition_2_7.english",
        "2.8": DT / "ContinuousLattice/Constructions/proposition_2_8.english",
        "2.9": DT / "ContinuousLattice/Constructions/proposition_2_9.english",
        "2.10": DT / "ContinuousLattice/Constructions/proposition_2_10.english",
        "2.11": DT / "ContinuousLattice/Constructions/1972_Proposition_2_11.english",
        "2.12": DT / "ContinuousLattice/ContinuousLattices/1972_Theorem_2_12.english",
        "proof_2.9": DT / "ContinuousLattice/Constructions/proposition_2_9.english",
        "proof_2.10": DT / "ContinuousLattice/Constructions/proposition_2_10.english",
        "proof_2.11": DT / "ContinuousLattice/Constructions/1972_Proposition_2_11.english",
        "sec3": DT / "ContinuousLattice/FunctionSpaces/1972_Definition_3_1.english",
        "3.1": DT / "ContinuousLattice/FunctionSpaces/1972_Definition_3_1.english",
        "3.2": DT / "ContinuousLattice/FunctionSpaces/1972_Proposition_3_2.english",
        "3.3": DT / "ContinuousLattice/FunctionSpaces/1972_Theorem_3_3.english",
        "3.4": DT / "ContinuousLattice/FunctionSpaces/1972_Corollary_3_4.english",
        "3.5": DT / "ContinuousLattice/FunctionSpaces/1972_Proposition_3_5.english",
        "3.6": DT / "ContinuousLattice/FunctionSpaces/1972_Definition_3_6.english",
        "3.7": DT / "ContinuousLattice/FunctionSpaces/1972_Proposition_3_7.english",
        "3.8": DT / "ContinuousLattice/Constructions/1972_Proposition_3_8.english",
        "3.9": DT / "ContinuousLattice/FunctionSpaces/1972_Lemma_3_9.english",
        "3.10": DT / "ContinuousLattice/FunctionSpaces/1972_Proposition_3_10.english",
        "3.11": DT / "ContinuousLattice/FunctionSpaces/1972_Definition_3_11.english",
        "3.12": DT / "ContinuousLattice/FunctionSpaces/proposition_3_12.english",
        "3.13": DT / "ContinuousLattice/FunctionSpaces/proposition_3_13.english",
        "3.14": DT / "ContinuousLattice/FunctionSpaces/1972_Proposition_3_14.english",
        # §4 hub is a roadmap; review OCR is parceled in bridge_sec4_review.
        "sec4": TBD / "sec4_review_before_4_1.english",
        "4.1": DT / "ContinuousLattice/InverseLimits/proposition_4_1.english",
        "4.2": DT / "ContinuousLattice/InverseLimits/1972_Proposition_4_2.english",
        "4.3": DT / "ContinuousLattice/InverseLimits/corollary_4_3.english",
        "4.4": DT / "ContinuousLattice/FunctionSpaceTower/1972_Theorem_4_4.english",
        "4.5": DT / "ContinuousLattice/InverseLimits/1972_Lemma_4_5.english",
        "proof_4.4": DT / "ContinuousLattice/FunctionSpaceTower/1972_Theorem_4_4.english",
        "correction": DT / "ContinuousLattice/MilnerCorrection/1972_Correction.english",
        "sec4_projections_figure": TBD / "sec4_projection_figures.english",
    }
    if key in m:
        return m[key]
    return TBD / f"{key}.english"


APPEND_KEYS = {"abstract", "sec0", "proof_2.9", "proof_2.10", "proof_2.11", "proof_4.4", "sec4_projections_figure"}


def bridge_before_sec2(lines: list[str], i_sec2: int, i_21: int) -> None:
    """Specialization / way-below lead-in between section 2 header and 2.1."""
    chunk = "\n".join(lines[i_sec2:i_21]).strip()
    if not chunk:
        return
    # split at way-below paragraph start
    wb = "Given a complete lattice"
    if wb in chunk:
        a, b = chunk.split(wb, 1)
        spec = (DT / "ContinuousLattice/Specialization/1972_Specialization.english")
        way = DT / "ContinuousLattice/WayBelow/1972_WayBelow.english"
        spec.parent.mkdir(parents=True, exist_ok=True)
        spec.write_text(a.strip() + "\n", encoding="utf-8")
        way.write_text(wb + b.strip() + "\n", encoding="utf-8")
    else:
        path_for_key("sec2").write_text(chunk + "\n", encoding="utf-8")


def bridge_sec1_post_17(lines: list[str], i_17: int, i_sec2: int) -> None:
    chunk = "\n".join(lines[i_17:i_sec2]).strip()
    if chunk:
        p = DT / "ContinuousLattice/Injective/1972_Absolute_retracts.english"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(chunk + "\n", encoding="utf-8")


def bridge_sec2_post_212(lines: list[str], i_212: int, i_sec3: int) -> None:
    chunk = "\n".join(lines[i_212:i_sec3]).strip()
    if chunk:
        p = TBD / "sec2_after_theorem_2_12.english"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(chunk + "\n", encoding="utf-8")


def bridge_sec3_mid(lines: list[str], i_35: int, i_36: int) -> None:
    chunk = "\n".join(lines[i_35:i_36]).strip()
    if chunk:
        p = TBD / "sec3_before_3_6.english"
        p.write_text(chunk + "\n", encoding="utf-8")


SEC4_HUB_ROADMAP = """\
Scott’s §4 opens with a review of inverse limits for $T_0$-spaces: an [inverse system and compatible sequences](InverseLimits/1972_Compatibility.md), the formal [inverse limit](InverseLimits/1972_InverseLimit.md) type for $\\langle D_n,P_n\\rangle$, [projections from the limit](InverseLimits/1972_Projections_from_the_limit.md) ($j_{\\infty n}$), the [mediating map](InverseLimits/1972_Mediating_map.md) into $X_\\infty$, and the turn to [special inverse systems](InverseLimits/1972_Special_inverse_systems.md). The notes that follow build the projection tower ($\\mathrm{projectionAlongTower}$, adjunction at one step), embeddings into the limit, lattice and topology on $D_\\infty$, and Propositions 4.1–4.4.
"""

COMPATIBILITY_LIBRARY_TAIL = """
For the continuous-lattice tower $\\langle D_n, P_n \\rangle$, $j_n$ is **`(P n).retr`**.

**Definition (`Compatible`).** **`Compatible D P x`** holds when $\\forall n,\\; (P\\,n).\\mathrm{retr}\\,(x\\,(n+1)) = x\\,n$ for **`x : ∀ n, D n`**.
"""

INVERSELIMIT_LIBRARY = """\
The preceding paragraphs describe $X_\\infty$ as the subspace of compatible sequences. For $\\langle D_n, P_n \\rangle$ the library name is **`InverseLimit D P`**.

**Definition (`InverseLimit`).** **`InverseLimit D P`** is the subtype of tuples **`x : ∀ n, D n`** that satisfy [**`Compatible`**](1972_Compatibility.md) (Scott’s $D_\\infty$ before topology and lattice structure are imposed).
"""

PROJINF_LIBRARY_TAIL = """
On **`InverseLimit D P`**, **`limitProjectionToLevel n`** is Scott’s $j_{\\infty n}$: the $n$-th coordinate **`y.1 n`**, packaged as a **`ScottMap`** once directed suprema on the limit are available.
"""


def bridge_sec4_review(lines: list[str], idx) -> None:
    """Parcel Scott's §4 review (before 4.1) into InverseLimits note sidecars."""
    i4 = idx("**4. INVERSE LIMITS.**")
    i41 = idx("**4.1 Proposition.**")
    text = "\n".join(lines[i4:i41]).strip()
    banner = "**4. INVERSE LIMITS.** "
    if text.startswith(banner):
        text = text[len(banner) :].strip()
    text = "\n".join(ln for ln in text.splitlines() if not re.fullmatch(r"\d{2,3}", ln.strip())).strip()
    p2 = text.index("The space $X_{\\infty}$ is given the product topology")
    p3 = text.index("Besides this we have the expected extension property")
    p4 = text.index("So much for a review of inverse limits.")
    p1, p2_text, p3_text, p4_text = (
        text[:p2].strip(),
        text[p2:p3].strip(),
        text[p3:p4].strip(),
        text[p4:].strip(),
    )
    inv = DT / "ContinuousLattice/InverseLimits"
    (DT / "ContinuousLattice/1972_4_Inverse_limits.english").write_text(SEC4_HUB_ROADMAP + "\n", encoding="utf-8")
    (inv / "1972_Compatibility.english").write_text(p1 + COMPATIBILITY_LIBRARY_TAIL + "\n", encoding="utf-8")
    (inv / "1972_InverseLimit.english").write_text(INVERSELIMIT_LIBRARY + "\n", encoding="utf-8")
    (inv / "1972_Projections_from_the_limit.english").write_text(
        p2_text + PROJINF_LIBRARY_TAIL + "\n", encoding="utf-8"
    )
    (inv / "1972_Mediating_map.english").write_text(p3_text + "\n", encoding="utf-8")
    (inv / "1972_Special_inverse_systems.english").write_text(p4_text + "\n", encoding="utf-8")


def main() -> None:
    lines = load_body_lines()
    indices = [i for i, line in enumerate(lines) if MARKER.match(line.strip())]
    if not indices:
        raise SystemExit("no markers found")

    buckets: dict[Path, list[str]] = {}
    for j, start in enumerate(indices):
        end = indices[j + 1] if j + 1 < len(indices) else len(lines)
        key = segment_key(lines[start])
        path = path_for_key(key)
        text = "\n".join(lines[start:end]).strip()
        if not text:
            continue
        if key in APPEND_KEYS and path in buckets:
            buckets[path].append(text)
        elif key in APPEND_KEYS and path.exists():
            prev = path.read_text(encoding="utf-8").strip()
            buckets[path] = [prev, text] if prev else [text]
        else:
            buckets.setdefault(path, []).append(text)

    TBD.mkdir(parents=True, exist_ok=True)
    for path, parts in buckets.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        body = "\n\n".join(p.strip() for p in parts if p.strip()) + "\n"
        path.write_text(body, encoding="utf-8")

    # named bridges (content between numbered markers)
    def idx(sub: str) -> int:
        for i, line in enumerate(lines):
            if sub in line:
                return i
        raise ValueError(sub)

    # After 1.7 proof (absolute retracts / lattice-structure lead-in)
    i_abs = next(i for i, ln in enumerate(lines) if ln.startswith("As a result of these"))
    bridge_sec1_post_17(lines, i_abs, idx("**2. CONTINUOUS LATTICES"))
    bridge_before_sec2(lines, idx("**2. CONTINUOUS LATTICES"), idx("**2.1 Proposition"))
    bridge_sec2_post_212(lines, idx("**2.12 Theorem"), idx("**3. FUNCTION SPACES"))
    # 3.5 ends ~743, 3.6 at 775
    try:
        bridge_sec3_mid(lines, idx("**3.5 Proposition"), idx("**3.6 Definition"))
    except ValueError:
        pass
    bridge_sec4_review(lines, idx)

    # mark unmapped TBD files in index
    tbd_index = TBD / "README.english"
    tbd_files = sorted(TBD.glob("*.english"))
    if tbd_files:
        tbd_index.write_text(
            "**TBD — prose not yet mapped to a note**\n\n"
            + "\n".join(f"- `{p.name}`" for p in tbd_files if p.name != "README.english")
            + "\n",
            encoding="utf-8",
        )

    # verify all source lines appear in outputs
    slotted = "\n".join(
        p.read_text(encoding="utf-8")
        for p in sorted(DT.rglob("*.english"))
        if "1972_TBD" not in str(p) or True
    )
    missing = [ln for ln in lines if ln.strip() and ln.strip() not in slotted and not ln.startswith("# CONTINUOUS")]
    # page-only lines allowed
    missing = [ln for ln in missing if not re.fullmatch(r"\d{2,3}", ln.strip())]
    print(f"wrote {len(buckets)} segment targets under {DT.relative_to(ROOT)}")
    print(f"TBD files: {len(list(TBD.glob('*.english')))}")
    if missing:
        orphan = TBD / "orphan_lines.english"
        orphan.write_text(
            "**TBD — lines not matched verbatim in slotted files**\n\n"
            + "\n".join(missing[:200])
            + ("\n..." if len(missing) > 200 else "")
            + "\n",
            encoding="utf-8",
        )
        print(f"warning: {len(missing)} source lines not found verbatim in outputs -> {orphan.name}")


if __name__ == "__main__":
    main()
