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









/-- **Theorem 2.5 — left identity law.** `I_{D₁} ∘ f = f`. (`→`: a witness `Y ⊆ Z` widens the output
of `f` by `f.mono`; `←`: take `Y = Z`.) -/
theorem idMap_comp (f : ApproximableMap V₀ V₁) : (idMap V₁).comp f = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨Y, hXY, _, hZ, hYZ⟩
    exact f.mono hXY subset_rfl hYZ (f.rel_dom hXY) hZ
  · intro hXZ
    exact ⟨Z, hXZ, f.rel_cod hXZ, f.rel_cod hXZ, subset_rfl⟩

end ApproximableMap
end DomainTheory.Neighborhood
