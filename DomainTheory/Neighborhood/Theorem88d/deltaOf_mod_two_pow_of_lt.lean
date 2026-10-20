/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88b
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.Theorem88d.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)











































/-- Reducing modulo `2ⁿ` never disturbs bits strictly below `n`. -/
theorem deltaOf_mod_two_pow_of_lt {k n i : ℕ} (hi : i < n) :
    deltaOf (k % 2 ^ n) i = deltaOf k i := by
  rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.testBit_mod_two_pow]
  simp [hi]

end DomainTheory.Neighborhood
