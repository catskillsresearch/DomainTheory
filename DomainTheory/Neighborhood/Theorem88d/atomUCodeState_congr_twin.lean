/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88b
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.Theorem88d.Basic
import DomainTheory.Neighborhood.Theorem88d.deltaOf_mod_two_pow_of_lt


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

























































/-- **The canonical "positive twin" at depth `n`** shares `k`'s own `(pos, neg, code)` triple, since
it agrees with `k` on every bit below `n` (`atomUCodeState_congr` applied to
`k % 2ⁿ`/`deltaOf_mod_two_pow_of_lt`/`deltaOf_add_two_pow_of_lt`). -/
theorem atomUCodeState_congr_twin (n k : ℕ) :
    atomUPos P n (k % 2 ^ n + 2 ^ n) = atomUPos P n k ∧
      atomUNeg P n (k % 2 ^ n + 2 ^ n) = atomUNeg P n k ∧
      atomUCode P n (k % 2 ^ n + 2 ^ n) = atomUCode P n k := by
  have hagree : ∀ i < n, deltaOf (k % 2 ^ n + 2 ^ n) i = deltaOf k i := by
    intro i hi
    rw [deltaOf_add_two_pow_of_lt _ hi, deltaOf_mod_two_pow_of_lt hi]
  exact atomUCodeState_congr P hagree

end DomainTheory.Neighborhood
