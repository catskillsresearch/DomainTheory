/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise127
import DomainTheory.Neighborhood.Exercise328.Basic
import DomainTheory.Neighborhood.Exercise328.val_le_leastMap_toElementMap


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- The active values are bounded (by `f₀(x)`). -/
theorem leastMapVals_bounded {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) (x : V₀.Element) :
    V₁.Bounded (leastMapVals L hL x) := by
  refine ⟨(leastMap L hL hcons).toElementMap x, ?_⟩
  rintro w ⟨p, hp, hp1x, rfl⟩
  exact val_le_leastMap_toElementMap hL hcons hp hp1x

end DomainTheory.Neighborhood
