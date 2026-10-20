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
import DomainTheory.Neighborhood.Exercise723.mem_sumSet
import DomainTheory.Neighborhood.Exercise723.plusIdx_testBit


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

























/-- **`plusIdx`'s excluded set is the Minkowski sum `Eₙ + Eₘ`.** -/
theorem compl_nbhd_plusIdx (n m : ℕ) : (nbhd (plusIdx n m))ᶜ = (nbhd n)ᶜ +ˢ (nbhd m)ᶜ := by
  rw [compl_nbhd, compl_nbhd, compl_nbhd]
  ext k
  simp only [mem_sumSet, Set.mem_ofPred_eq, plusIdx_testBit]
  constructor
  · rintro ⟨a, hak, ha, hb⟩; exact ⟨a, ha, k - a, hb, by omega⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, by omega, ha, by rw [Nat.add_sub_cancel_left]; exact hb⟩

end DomainTheory.Neighborhood.Exercise723
