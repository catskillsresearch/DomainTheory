/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Exercise122
import DomainTheory.Neighborhood.Exercise213.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


namespace NeighborhoodSystem


/-- **Exercise 2.13 — Scott's union formula for a continuous map.** For continuous `c` and any
`x ∈ |𝒟₀|`: `Y ∈ c(x) ↔ ∃ X ∈ x, Y ∈ c(↑X)`.

* `→` : `c⁻¹[[Y]]` is open and contains `x`, so it contains a basic neighbourhood `[X]` with `X ∈ x`;
  since `↑X ∈ [X]`, `Y ∈ c(↑X)`.
* `←` : `↑X ⊑ x` and `c` monotone (`continuous_monotone`) give `c(↑X) ⊑ c(x)`, transporting `Y`. -/
theorem mem_iff_principal_of_continuous {c : V₀.Element → V₁.Element} (hc : Continuous c)
    (x : V₀.Element) {Y : Set β} :
    (c x).mem Y ↔ ∃ (X : Set α) (hx : x.mem X), (c (V₀.principal (x.sub hx))).mem Y := by
  constructor
  · intro hY
    have hxpre : x ∈ c ⁻¹' V₁.basicOpen Y := hY
    have hopen : IsOpen (c ⁻¹' V₁.basicOpen Y) := (V₁.isOpen_basicOpen Y).preimage hc
    obtain ⟨X, hxX, hXU⟩ := hopen x hxpre
    refine ⟨X, hxX, ?_⟩
    exact hXU (show V₀.principal (x.sub hxX) ∈ V₀.basicOpen X from ⟨x.sub hxX, subset_rfl⟩)
  · rintro ⟨X, hxX, hY⟩
    have hple : V₀.principal (x.sub hxX) ≤ x := fun Z hZ => x.up_mem hxX hZ.1 hZ.2
    exact (continuous_monotone hc hple) Y hY

end NeighborhoodSystem
end DomainTheory.Neighborhood
