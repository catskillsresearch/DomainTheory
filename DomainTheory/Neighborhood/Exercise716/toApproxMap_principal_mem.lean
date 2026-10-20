/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem75
import DomainTheory.Neighborhood.Table55
import DomainTheory.Neighborhood.Exercise716.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}



/-- The least map of a function-space neighbourhood `G` — `toApproxMap ↑G` — belongs to `G`. -/
theorem toApproxMap_principal_mem {G : Set (ApproximableMap V₀ V₁)}
    (hG : (funSpace V₀ V₁).mem G) : toApproxMap ((funSpace V₀ V₁).principal hG) ∈ G := by
  obtain ⟨L, hL, rfl⟩ := hG.1
  intro p hp
  show (toApproxMap ((funSpace V₀ V₁).principal hG)).rel p.1 p.2
  rw [toApproxMap_rel, mem_principal]
  exact ⟨step_mem (hL p hp).1 (hL p hp).2, fun f hf => hf p hp⟩

end DomainTheory.Neighborhood
