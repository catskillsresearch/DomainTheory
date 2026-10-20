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


namespace DomainTheory.Neighborhood.Exercise723

open DomainTheory.Neighborhood Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.Neighborhood.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.Neighborhood.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)
















/-- `cupMap`'s neighbourhood relation on indices: `nbhd n ∪ nbhd m` relates to `nbhd k` iff
`nbhd (myLor n m) ⊆ nbhd k`. -/
theorem cupMap_rel_iff (n m k : ℕ) :
    cupMap.rel (prodNbhd (nbhd n) (nbhd m)) (nbhd k) ↔ nbhd (myLor n m) ⊆ nbhd k := by
  rw [← nbhd_inter n m]
  constructor
  · rintro ⟨X, Y, heq, _, _, _, hXYZ⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact hXYZ
  · intro h
    exact ⟨nbhd n, nbhd m, rfl, ⟨n, rfl⟩, ⟨m, rfl⟩, ⟨k, rfl⟩, h⟩

end DomainTheory.Neighborhood.Exercise723
