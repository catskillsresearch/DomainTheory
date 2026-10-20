/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise127
import DomainTheory.Neighborhood.FunctionSpace.Basic
import DomainTheory.Neighborhood.FunctionSpace.leastMap_mem_stepFun
import DomainTheory.Neighborhood.FunctionSpace.rel_interYs


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}








































/-- **Remark after Proposition 3.9 (Scott 1981, PRG-19).** When the neighbourhood is consistent,
`⋂ [Xᵢ, Yᵢ] ⊆ [X, Y]` iff `⋂{Yᵢ ∣ X ⊆ Xᵢ} ⊆ Y`. This is the form used to check that `curry` is
monotone (and hence approximable). -/
theorem stepFun_subset_step_iff {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {X : Set α} {Y : Set β}
    (hX : V₀.mem X) (hY : V₁.mem Y) :
    (stepFun L : Set (ApproximableMap V₀ V₁)) ⊆ step X Y ↔ interYs V₁.master L X ⊆ Y := by
  constructor
  · intro hsub
    have := hsub (leastMap_mem_stepFun hL hcons)
    exact (mem_step.mp this).2.2
  · intro hsub f hf
    exact f.mono (rel_interYs hf hX) subset_rfl hsub hX hY

end DomainTheory.Neighborhood
