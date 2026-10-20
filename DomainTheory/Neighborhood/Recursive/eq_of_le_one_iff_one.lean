/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import Mathlib.Computability.Partrec
import Mathlib.Tactic.Ring
import DomainTheory.Neighborhood.Exercise722Regular
import DomainTheory.Neighborhood.Exercise722Decide
import DomainTheory.Neighborhood.Exercise722Equiv
import DomainTheory.Neighborhood.Recursive.Basic


namespace Domain.Recursive







































































































/-- Two `{0,1}`-bounded naturals agreeing on "`= 1`" are equal. -/
theorem eq_of_le_one_iff_one {x y : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) (h : x = 1 ↔ y = 1) : x = y := by
  by_cases hx1 : x = 1
  · have hy1 := h.mp hx1; omega
  · have hy1 : y ≠ 1 := fun hy1 => hx1 (h.mpr hy1)
    omega

end Domain.Recursive
