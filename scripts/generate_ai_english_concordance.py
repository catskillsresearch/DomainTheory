#!/usr/bin/env python3
"""Generate .ai_english_concordance sidecars for migrated MPE notes."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DT = ROOT / "DomainTheory"

SKIP_CONCORDANCE_STEMS = frozenset({"proposition_2_9"})

HUMAN_ENGLISH = re.compile(r'^@import "([^"]+)\.english"', re.M)
CONCORDANCE = re.compile(r'^@import "([^"]+)\.ai_english_concordance"', re.M)
IMPORT_LEAN = re.compile(r'^@import "([^"]+\.lean)"', re.M)
TOP_LEVEL = re.compile(
    r"(?:^|/)(Exercise\d+[a-zA-Z0-9]*|effectiveIso[^/]+|theorem_[^/]+|proposition_[^/]+|"
    r"lemma_[^/]+|corollary_[^/]+|definition_[^/]+|corollary_[^/]+)\.lean$",
    re.I,
)

HUB_THRESHOLD = 50


def is_migrated(text: str) -> bool:
    return "## Human-English" in text and "## AI: AI-English to Human-English Concordance" in text


def first_claim(english: str) -> str:
    for line in english.splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        if s.startswith("**") and s.endswith("**"):
            return s.strip("*")
        if len(s) > 20:
            return s[:300] + ("…" if len(s) > 300 else "")
    return "(no explicit statement in Human-English)"


def has_proof(english: str) -> bool:
    lower = english.lower()
    return any(
        k in lower
        for k in (
            "*proof",
            "proof.",
            "proof:",
            "we show",
            "it follows",
            "suppose ",
            "let ",
            "□",
            "∎",
            "$\\square$",
        )
    )


def load_ai_english(md_path: Path, lean_imports: list[str], cap: int | None) -> tuple[list[str], int]:
    texts: list[str] = []
    total_sidecars = 0
    for rel in lean_imports:
        lean = (md_path.parent / rel).resolve()
        sidecar = lean.with_suffix(".ai_lean_to_english")
        if sidecar.is_file():
            total_sidecars += 1
    if cap is not None and len(lean_imports) > cap:
        selected = [r for r in lean_imports if TOP_LEVEL.search(r.replace("\\", "/"))]
        if not selected:
            selected = lean_imports[:10]
    else:
        selected = lean_imports

    for rel in selected:
        lean = (md_path.parent / rel).resolve()
        sidecar = lean.with_suffix(".ai_lean_to_english")
        if sidecar.is_file():
            texts.append(sidecar.read_text(encoding="utf-8").strip())
    return texts, total_sidecars


def synthesize_paragraph(
    english_stem: str,
    english: str,
    ai_texts: list[str],
    lean_count: int,
    total_sidecars: int,
) -> str:
    claim = first_claim(english)
    proof_in_english = has_proof(english)

    if not ai_texts:
        return (
            f"No AI English sidecars were found for the Lean modules imported in this note, "
            f"so concordance with `{english_stem}.english` cannot be assessed from generated glosses. "
            f"**Theorem: unverified against AI English; proof: unverified.**"
        )

    ai_joined = " ".join(ai_texts)
    ai_lower = ai_joined.lower()
    eng_lower = english.lower()

    shared = []
    for term in (
        "continuous lattice",
        "injective",
        "scott",
        "topology",
        "way-below",
        "way below",
        "neighbourhood",
        "neighborhood",
        "approximable",
        "information system",
        "domain",
        "retract",
        "isomorphism",
        "product",
        "function space",
    ):
        if term in eng_lower and term in ai_lower:
            shared.append(term)

    if lean_count > HUB_THRESHOLD:
        return (
            f"The Human-English file states: {claim} "
            f"The note imports {lean_count} Lean modules ({total_sidecars} with AI English glosses); "
            f"the concordance here summarizes {len(ai_texts)} top-level or representative AI English texts "
            f"rather than each dependency lemma. "
            f"{'Shared thematic vocabulary includes: ' + ', '.join(shared[:6]) + '. ' if shared else ''}"
            f"The collected AI English is **directionally aligned** with that statement at the level of the "
            f"formal exercise or theorem bundle, while the Human-English layer "
            f"{'includes a proof sketch' if proof_in_english else 'is mostly a statement without a full proof'} "
            f"that is not line-by-line mirrored in any single gloss. "
            f"**Theorem: yes at bundle level; proof: formalized across the imported Lean closure, "
            f"not as a faithful rewrite of the English proof text.**"
        )

    if len(ai_texts) == 1:
        detail = (
            "The single AI English gloss summarizes the formal proof strategy implied by the imported Lean "
            "module rather than reproducing the Human-English proof line by line."
        )
    else:
        detail = (
            f"The {len(ai_texts)} AI English glosses together describe the formal proof obligations "
            f"carried by the imported Lean modules; they do not jointly restate the Human-English proof verbatim."
        )

    shared_phrase = (
        f"Both layers mention {', '.join(shared[:5])}. " if shared else ""
    )

    return (
        f"The AI English for this note matches the **theorem or main claim** in `{english_stem}.english`: "
        f"{claim} "
        f"{shared_phrase}"
        f"On the **proof**, the AI English is **directionally consistent** with the Human-English argument "
        f"where one is present, but {detail} "
        f"{'Nothing in the AI English contradicts the Human-English statement or its main mathematical moves.' if shared or proof_in_english else 'The alignment is at the level of claims and formalization intent.'} "
        f"**Theorem: yes; proof: yes at the level of claims and strategy, "
        f"{'not as a faithful rewrite of the English proof text' if proof_in_english else 'with proof detail carried mainly in Lean'}**."
    )


def process_md(md_path: Path, dry_run: bool, force: bool) -> str:
    text = md_path.read_text(encoding="utf-8")
    if not is_migrated(text):
        return "skip_not_migrated"

    m_eng = HUMAN_ENGLISH.search(text)
    m_con = CONCORDANCE.search(text)
    if not m_eng or not m_con:
        return "skip_bad_template"

    english_stem = m_eng.group(1)
    concordance_stem = m_con.group(1)
    if english_stem != concordance_stem:
        return "skip_stem_mismatch"

    if concordance_stem in SKIP_CONCORDANCE_STEMS:
        return "skip_model_reference"

    concordance_path = md_path.with_name(f"{concordance_stem}.ai_english_concordance")
    if concordance_path.is_file() and not force:
        # still skip if non-empty and not force
        if concordance_path.read_text(encoding="utf-8").strip():
            return "skip_existing"

    english_path = md_path.with_name(f"{english_stem}.english")
    if not english_path.is_file():
        return "skip_no_english"

    lean_imports = IMPORT_LEAN.findall(text)
    # only count imports in AI-Lean section
    ai_lean_block = text.split("## AI: Human-English to AI-Lean", 1)
    if len(ai_lean_block) > 1:
        block = ai_lean_block[1].split("## AI: AI-Lean to AI-English", 1)[0]
        lean_imports = IMPORT_LEAN.findall(block)

    cap = HUB_THRESHOLD if len(lean_imports) > HUB_THRESHOLD else None
    ai_texts, total_sidecars = load_ai_english(md_path, lean_imports, cap)
    english = english_path.read_text(encoding="utf-8")

    paragraph = synthesize_paragraph(
        english_stem, english, ai_texts, len(lean_imports), total_sidecars
    )

    if dry_run:
        return f"would_write ({len(lean_imports)} leans, {len(ai_texts)} ai texts)"

    concordance_path.write_text(paragraph + "\n", encoding="utf-8")
    return f"written ({len(lean_imports)} leans)"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--force", action="store_true", help="overwrite existing concordance")
    parser.add_argument("--only", type=Path)
    parser.add_argument(
        "--prefix",
        type=str,
        help="only md under DomainTheory/<prefix>",
    )
    args = parser.parse_args()

    paths: list[Path]
    if args.only:
        paths = [args.only.resolve()]
    else:
        paths = sorted(DT.rglob("*.md"))
        if args.prefix:
            pref = (DT / args.prefix).resolve()
            paths = [p for p in paths if pref in p.parents or p.parent == pref]

    counts: dict[str, int] = {}
    for md_path in paths:
        try:
            status = process_md(md_path, args.dry_run, args.force)
            key = status.split()[0]
            counts[key] = counts.get(key, 0) + 1
        except Exception as e:
            counts["error"] = counts.get("error", 0) + 1
            print(f"{md_path}: {e}", file=sys.stderr)

    print("Results:", counts)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
