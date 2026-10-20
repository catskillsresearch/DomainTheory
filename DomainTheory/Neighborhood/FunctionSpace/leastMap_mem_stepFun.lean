/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise127
import DomainTheory.Neighborhood.FunctionSpace.Basic
import DomainTheory.Neighborhood.FunctionSpace.interYs_subset_of_mem


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}








































/-- **Proposition 3.9 (Scott 1981, PRG-19).** The least map `f₀` belongs to the neighbourhood:
`Xᵢ f₀ Yᵢ` for every `(Xᵢ, Yᵢ) ∈ L`. -/
theorem leastMap_mem_stepFun {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) : leastMap L hL hcons ∈ stepFun L := by
  intro p hp
  exact ⟨(hL p hp).1, (hL p hp).2, interYs_subset_of_mem hp⟩

end DomainTheory.Neighborhood
