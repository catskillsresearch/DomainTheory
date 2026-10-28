#!/usr/bin/env python3
"""Sanitize Lean sources for ``\\lstinputlisting`` in the arXiv pdfLaTeX build.

Listings use the ``leanbox`` ``listings`` style in ``tex_preamble_arxiv.tex``: each
Lean operator that appears in source should stay as UTF-8 and is rendered via a
``literate`` mapping.  Characters *not* in that table are either rewritten to
readable ASCII or replaced with ``?`` so pdfLaTeX never sees unsupported bytes.

The allowlist is parsed from the preamble so it stays in sync with ``leanbox``.
"""

from __future__ import annotations

import re
import unicodedata
from functools import lru_cache
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
_PREAMBLE = _SCRIPTS / "tex_preamble_arxiv.tex"

_LEANBOX_LITERATE_RE = re.compile(r"\{([^}]+)\}\{\{")

# Order matters: longer / composite replacements first where needed.
LEAN_UNICODE_REPLACEMENTS: tuple[tuple[str, str], ...] = (
    # Composites (including combining-mark spellings used in docstrings)
    ("⋢", " sqsubneq "),
    ("⊑\u0338", " sqsubneq "),
    ("⁻¹", "^-1"),
    ("⟶", " --> "),
    ("⟷", " <-> "),
    ("⟨", "<"),
    ("⟩", ">"),
    ("↦", " |-> "),
    ("⊢", " |- "),
    ("⊨", " |= "),
    ("⊬", " |/- "),
    ("⊭", " |/= "),
    # modal / hybrid operators
    ("□", "[] "),
    ("◇", "<> "),
    ("∼", "~"),
    ("⋀", " /\\ "),
    ("⋁", " \\/ "),
    # logical connectives / quantifiers
    ("∀", "forall "),
    ("∃", "exists "),
    ("¬", "not "),
    ("∧", " /\\ "),
    ("∨", " \\/ "),
    ("↔", " <-> "),
    ("→", " -> "),
    ("←", " <- "),
    ("⇒", " => "),
    ("⊥", "False"),
    # set theory
    ("∈", " in "),
    ("∉", " notin "),
    ("∪", " U "),
    ("∩", " I "),
    ("⊆", " subseteq "),
    ("⊇", " supseteq "),
    ("∅", "{}"),
    # relations
    ("≠", " != "),
    ("≤", " <= "),
    ("≥", " >= "),
    ("≅", " ~= "),
    ("≪", " << "),
    ("⊑", " sqsub "),
    ("⊔", " sqsup "),
    ("⊓", " sqcap "),
    ("⊤", " top "),
    ("⊣", " dashv "),
    ("↟", " Up "),
    ("⇄", " <=> "),
    ("⨆", " bigcup "),
    ("𝕆", " O "),
    ("∞", " inf "),
    ("′", "'"),
    ("ḡ", "g"),
    ("̄", ""),  # combining macron (often after explicit pairs above)
    ("̸", ""),  # combining long slash overlay
    # arrows / misc operators
    ("↑", ""),
    ("↓", ""),
    ("↥", ""),
    ("▸", " |> "),
    ("∘", " comp "),
    ("·", "*"),
    ("×", " x "),
    ("§", "S"),
    ("—", "--"),
    ("–", "-"),
    ("…", "..."),
    # Greek letters (identifiers in Lean source)
    ("Γ", "Gamma"),
    ("Δ", "Delta"),
    ("Θ", "Theta"),
    ("Σ", "Sigma"),
    ("Η", "Eta"),
    ("Κ", "Kappa"),
    ("φ", "phi"),
    ("ψ", "psi"),
    ("χ", "chi"),
    ("σ", "sigma"),
    ("τ", "tau"),
    ("α", "a"),
    ("β", "b"),
    ("λ", "fun "),
    # double-struck / blackboard
    ("ℕ", "Nat"),
    ("ℤ", "Int"),
    # sub/superscripts (fallback when not using literate — normally skipped)
    ("₀", "_0"),
    ("₁", "_1"),
    ("₂", "_2"),
    ("₃", "_3"),
    ("ₙ", "_n"),
    ("ₚ", "_p"),
    ("ᵢ", "_i"),
    ("₊", "_+"),
    ("⁺", "^+"),
    ("⁻", "^-"),
    ("¹", "1"),
    # box drawing (set-builder bars and ASCII-art flowcharts in fenced blocks)
    ("│", "|"),
    ("─", "-"),
    ("━", "-"),
    ("├", "+"),
    ("┤", "+"),
    ("┬", "+"),
    ("┴", "+"),
    ("┼", "+"),
    ("┌", "+"),
    ("┐", "+"),
    ("└", "+"),
    ("┘", "+"),
    ("╭", "+"),
    ("╮", "+"),
    ("╰", "+"),
    ("╯", "+"),
    ("║", "|"),
    ("═", "="),
    ("╔", "+"),
    ("╗", "+"),
    ("╚", "+"),
    ("╝", "+"),
    ("╠", "+"),
    ("╣", "+"),
    ("•", "*"),
    ("▪", "*"),
    ("▶", ">"),
    ("◀", "<"),
    ("╱", "/"),
    ("╲", "\\"),
    ("○", "o"),
    ("∿", "~"),
    ("≃", " ~= "),
)


@lru_cache(maxsize=1)
def leanbox_literate_chars(*, preamble_path: Path | None = None) -> frozenset[str]:
    """Characters the ``leanbox`` listing style renders via ``literate``."""
    path = preamble_path or _PREAMBLE
    text = path.read_text(encoding="utf-8")
    start = text.find("\\lstdefinestyle{leanbox}")
    if start < 0:
        raise RuntimeError(f"leanbox style not found in {path}")
    end = text.find("\\lstset{style=leanbox}", start)
    if end < 0:
        raise RuntimeError(f"leanbox literate block not terminated in {path}")
    block = text[start:end]
    chars: set[str] = set()
    for key in _LEANBOX_LITERATE_RE.findall(block):
        for ch in key:
            chars.add(ch)
    return frozenset(chars)


def _replacements_for_listings(allowed: frozenset[str]) -> tuple[tuple[str, str], ...]:
    """Drop ASCII fallbacks for glyphs ``leanbox`` already typesets."""
    out: list[tuple[str, str]] = []
    for src, dst in LEAN_UNICODE_REPLACEMENTS:
        if len(src) == 1 and src in allowed:
            continue
        out.append((src, dst))
    return tuple(out)


def sanitize_lean_for_arxiv(
    text: str,
    *,
    preamble_path: Path | None = None,
) -> str:
    allowed = leanbox_literate_chars(preamble_path=preamble_path)
    replacements = _replacements_for_listings(allowed)

    out = text
    for src, dst in replacements:
        out = out.replace(src, dst)
    out = unicodedata.normalize("NFD", out)
    out = "".join(c for c in out if unicodedata.category(c) != "Mn")
    return "".join(ch if ord(ch) < 128 or ch in allowed else "?" for ch in out)


def chunk_line_ranges(line_count: int, chunk_size: int = 350) -> list[tuple[int, int]]:
    if line_count <= chunk_size:
        return [(1, line_count)]
    ranges: list[tuple[int, int]] = []
    start = 1
    while start <= line_count:
        end = min(start + chunk_size - 1, line_count)
        ranges.append((start, end))
        start = end + 1
    return ranges
