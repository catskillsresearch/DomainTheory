/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Proposition710
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise719.Basic
import DomainTheory.Neighborhood.Exercise719.PDmem_mem


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}




/-- **Exercise 7.19 — `ℙ` preserves identity maps.** `ℙ(I_D) = I_{ℙD}`. The body
`∀ X ∈ A, ∃ Y ∈ B, X ⊆ Y` is equivalent to `A ⊆ B` by downward closure of `B`. -/
theorem PFmap_idMap (V : NeighborhoodSystem α) : PFmap (idMap V) = idMap V.PowerDomain := by
  apply ApproximableMap.ext
  intro A B
  simp only [PFmap_rel, idMap_rel]
  constructor
  · rintro ⟨hA, hB, hbody⟩
    refine ⟨hA, hB, ?_⟩
    intro X hX
    obtain ⟨Y, hYB, hXmem, _, hXY⟩ := hbody X hX
    exact V.PDmem_down hB hYB hXY hXmem
  · rintro ⟨hA, hB, hsub⟩
    refine ⟨hA, hB, ?_⟩
    intro X hX
    exact ⟨X, hsub hX, V.PDmem_mem hA hX, V.PDmem_mem hA hX, subset_rfl⟩

end DomainTheory.Neighborhood
