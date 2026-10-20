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









/-- **Theorem 2.5 — right identity law.** `f ∘ I_{D₀} = f`. (`→`: a witness `X ⊆ Y` sharpens the
input of `f` by `f.mono`; `←`: take `Y = X`.) -/
theorem comp_idMap (f : ApproximableMap V₀ V₁) : f.comp (idMap V₀) = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨Y, ⟨hX, _, hXY⟩, hYZ⟩
    exact f.mono hYZ hXY subset_rfl hX (f.rel_cod hYZ)
  · intro hXZ
    exact ⟨X, ⟨f.rel_dom hXZ, f.rel_dom hXZ, subset_rfl⟩, hXZ⟩

end ApproximableMap
end DomainTheory.Neighborhood
