/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import Mathlib.Data.Set.Image
import DomainTheory.Neighborhood.ApproximableExercises.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α β γ : Type*}





namespace ApproximableMap₂

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}



/-- **Exercise 2.19 (recovery of the relation).** `X, Y f Z ↔ Z ∈ f(↑X, ↑Y)`, the two-variable
analogue of Proposition 2.2(ii). -/
theorem rel₂_iff_mem_principal (f : ApproximableMap₂ V₀ V₁ V₂) {X : Set α} (hX : V₀.mem X)
    {Y : Set β} (hY : V₁.mem Y) {Z : Set γ} :
    f.rel X Y Z ↔ (f.toElementMap₂ (V₀.principal hX) (V₁.principal hY)).mem Z := by
  constructor
  · intro hrel
    exact ⟨X, Y, ⟨hX, subset_rfl⟩, ⟨hY, subset_rfl⟩, hrel⟩
  · rintro ⟨X', Y', ⟨_, hXX'⟩, ⟨_, hYY'⟩, hrel⟩
    exact f.mono hrel hXX' hYY' subset_rfl hX hY (f.rel_cod hrel)

end ApproximableMap₂
end DomainTheory.Neighborhood
