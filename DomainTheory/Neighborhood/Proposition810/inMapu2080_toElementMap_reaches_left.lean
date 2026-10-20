/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition89
import DomainTheory.Neighborhood.Definition83
import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.Proposition810.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}




/-- The image of `in₀` always reaches the left copy (witnessed by `V₀.master`, since `v.master_mem`
always holds and `in₀`'s relation only needs `inj₀ X ⊆ inj₀ V₀.master`). -/
theorem inMap₀_toElementMap_reaches_left {γ δ} {V₀ : NeighborhoodSystem γ} {V₁ : NeighborhoodSystem δ}
    {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} (v : V₀.Element) :
    ∃ X, V₀.mem X ∧ ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap v).mem (inj₀ X) := by
  refine ⟨V₀.master, V₀.master_mem, V₀.master, v.master_mem, V₀.master_mem, ?_, subset_rfl⟩
  exact Or.inr (Or.inl ⟨V₀.master, V₀.master_mem, rfl⟩)

end DomainTheory.Neighborhood
