/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic.Set
import DomainTheory.Neighborhood.Approximable.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

variable {α β γ δ : Type*}



namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}









/-- **Theorem 2.5 — associativity.** `h ∘ (g ∘ f) = (h ∘ g) ∘ f`. Pure reassociation of the
existential witnesses. -/
theorem comp_assoc {V₃ : NeighborhoodSystem δ} (h : ApproximableMap V₂ V₃)
    (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply ApproximableMap.ext
  intro X W
  constructor
  · rintro ⟨Y, hXY, Z, hYZ, hZW⟩
    exact ⟨Z, ⟨Y, hXY, hYZ⟩, hZW⟩
  · rintro ⟨Z, ⟨Y, hXY, hYZ⟩, hZW⟩
    exact ⟨Y, hXY, Z, hYZ, hZW⟩

end ApproximableMap
end DomainTheory.Neighborhood
