/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example78
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Exercise514
import DomainTheory.Neighborhood.Exercise723.Basic
import DomainTheory.Neighborhood.Exercise723.testBit_orUpTo


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)
























/-- **`orUpTo n m n` computes the Minkowski sum `Eₙ + Eₘ` exactly.** Every set bit `a` of `n`
satisfies `a < n` (`lt_of_testBit_true`), so ranging `a` over `N = n` sees every set bit of `n`. -/
theorem testBit_orUpTo_self (n m k : ℕ) :
    (orUpTo n m n).testBit k = true ↔ ∃ a, a ≤ k ∧ n.testBit a = true ∧ m.testBit (k - a) = true := by
  rw [testBit_orUpTo]
  constructor
  · rintro ⟨a, _, ha, hak, hb⟩; exact ⟨a, hak, ha, hb⟩
  · rintro ⟨a, hak, ha, hb⟩; exact ⟨a, lt_of_testBit_true ha, ha, hak, hb⟩

end DomainTheory.Neighborhood.Exercise723
