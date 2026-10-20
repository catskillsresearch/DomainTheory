/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise621
import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Exercise627.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}





theorem fstProj_comp_fstInj (D₀ D₁ : NeighborhoodSystem Str) :
    (fstProj D₀ D₁).comp (fstInj D₀ D₁) = idMap D₀ := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hX, _, hsub⟩, _, hZ, hsub'⟩
    exact ⟨hX, hZ, (prodTokNbhd_subset_iff.mp (hsub.trans hsub')).1⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨prodTokNbhd Z D₁.master,
      ⟨hX, prodTok_mem_prodTokNbhd hZ D₁.master_mem,
        prodTokNbhd_subset_iff.mpr ⟨hXZ, subset_rfl⟩⟩,
      prodTok_mem_prodTokNbhd hZ D₁.master_mem, hZ, subset_rfl⟩

end Exercise627
end DomainTheory.Neighborhood
