#!/usr/bin/env python3
"""Regression tests for post-Pandoc dollar unescaping."""

from __future__ import annotations

import sys
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(_SCRIPTS.parent))

from scripts.build_arxiv_tex import (  # noqa: E402
    _unescape_pandoc_dollar_signs,
    cleanup_pandoc_latex,
    pandoc_cites_to_latex_cite,
    pandoc_to_latex,
)


def test_unparsed_inline_math_outside_math() -> None:
    raw = r"the sets \$ y \in D : x \ll y \$ as a basis"
    out = _unescape_pandoc_dollar_signs(raw)
    assert out == r"the sets $ y \in D : x \ll y $ as a basis"


def test_mathbf_dollar_combinator_inside_math() -> None:
    raw = r"\(\mathbf{\$}\) and \[\mathbf{\$}(u)\]"
    out = _unescape_pandoc_dollar_signs(raw)
    assert out == raw


def test_pandoc_mathbf_dollar_end_to_end() -> None:
    md = r"combinator $\mathbf{\$}$ here"
    raw = pandoc_to_latex(md, shift=False)
    clean = cleanup_pandoc_latex(raw)
    assert r"\mathbf{\$}" in clean
    assert r"\mathbf{$}" not in clean


def test_pandoc_cites_to_latex_cite() -> None:
    assert pandoc_cites_to_latex_cite("[@Sco72]") == r"\cite{Sco72}"
    assert pandoc_cites_to_latex_cite("[@Scott70; @Scott71]") == r"\cite{Scott70,Scott71}"
    assert (
        pandoc_cites_to_latex_cite("[@Rogers67, pp. 146-147]")
        == r"\cite[pp.~146--147]{Rogers67}"
    )
    assert (
        pandoc_cites_to_latex_cite("[@Sco72, end of § 2]")
        == r"\cite[end of $\S$~2]{Sco72}"
    )
    # Lean-style attribute lists must not be rewritten.
    lean = "rw [@isOpen_iff_forall_mem_open _ (@Pi.topologicalSpace)]"
    assert pandoc_cites_to_latex_cite(lean) == lean


if __name__ == "__main__":
    test_unparsed_inline_math_outside_math()
    test_mathbf_dollar_combinator_inside_math()
    test_pandoc_mathbf_dollar_end_to_end()
    test_pandoc_cites_to_latex_cite()
    print("ok")
