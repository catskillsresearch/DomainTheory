/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import DomainTheory.DataTypesAsLattices.Pomega.Basic


namespace DomainTheory.DataTypesAsLattices



















theorem triangle_le_pair (n m : ℕ) :
    triangle (n + m) ≤ pair n m ∧ pair n m < triangle (n + m + 1) := by
  constructor
  · exact Nat.le_add_right _ _
  · rw [triangle_succ]
    exact Nat.add_lt_add_left (Nat.lt_succ_of_le (Nat.le_add_left m n)) _

end DomainTheory.DataTypesAsLattices
