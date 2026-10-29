#!/usr/bin/env python3
"""Tests for Lean listing sanitization (run: python3 scripts/test_lean_listing_sanitize.py)."""

from __future__ import annotations

import sys
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(_SCRIPTS))

from lean_listing_sanitize import (  # noqa: E402
    leanbox_literate_chars,
    sanitize_lean_for_arxiv,
)


def test_preserves_literate_math_notation() -> None:
    sample = (
        "Every injective `T₀`-space. Homeomorphism `D ≃ₜ IdempotentFixedPoint e`. "
        "Order iso `A ≃o E`. obtain ⟨ι, ⟨R⟩⟩"
    )
    out = sanitize_lean_for_arxiv(sample)
    assert "T_0" not in out, out
    assert "T₀" in out, out
    assert "??" not in out, out
    assert "≃ₜ" in out, out
    assert "≃o" in out, out
    assert "<?>," not in out, out
    assert "ι" in out, out


def test_still_ascii_falls_back_for_unknown() -> None:
    out = sanitize_lean_for_arxiv("unknown glyph: \U0001f600")
    assert "?" in out
    assert "\U0001f600" not in out


def test_literate_set_includes_core_operators() -> None:
    allowed = leanbox_literate_chars()
    for c in "₀≃ₜι∀∧→":
        assert c in allowed, repr(c)


def main() -> None:
    test_preserves_literate_math_notation()
    test_still_ascii_falls_back_for_unknown()
    test_literate_set_includes_core_operators()
    print("ok: lean_listing_sanitize")


if __name__ == "__main__":
    main()
