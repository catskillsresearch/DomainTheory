#!/usr/bin/env python3
"""Regression tests for Scott-style set comprehension repair (Pandoc-safe math)."""

from __future__ import annotations

import sys
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(_SCRIPTS.parent))

from scripts.compile_md_tree import (  # noqa: E402
    _repair_math_body,
    repair_bare_set_comprehensions,
)


def test_repair_bodies() -> None:
    assert _repair_math_body(r"y \in D : x \ll y") == r"\{ y \in D : x \ll y \}"
    assert _repair_math_body(r"y = \bigsqcup x \in D : x \ll y") == (
        r"y = \bigsqcup \{ x \in D : x \ll y \}"
    )
    assert _repair_math_body(r"y = \bigsqcup \sqcap U : y \in U") == (
        r"y = \bigsqcup \{ \sqcap U : y \in U \}"
    )
    assert _repair_math_body(r"z : z_i \in U") == r"\{ z : z_i \in U \}"


def test_inline_trim_and_braces() -> None:
    out = repair_bare_set_comprehensions(
        r"the set $ x : i(x) \sqsubseteq x' $ is directed"
    )
    assert out == r"the set $\{ x : i(x) \sqsubseteq x' \}$ is directed"


if __name__ == "__main__":
    test_repair_bodies()
    test_inline_trim_and_braces()
    print("ok")
