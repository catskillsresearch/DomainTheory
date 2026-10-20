/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Exercise127
import DomainTheory.Neighborhood.Exercise328.Basic
import DomainTheory.Neighborhood.Exercise328.Elementu2emem_interYs_of


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- `f₀(x)` is a *lower* bound of the upper bounds: any upper bound `z` of the active values
dominates `f₀(x)`. (Uses that `z` then contains `⋂{Yᵢ ∣ X ⊆ Xᵢ}`.) -/
theorem leastMap_toElementMap_le_of_ub {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {x : V₀.Element} {z : V₁.Element}
    (hz : ∀ w ∈ leastMapVals L hL x, w ≤ z) :
    (leastMap L hL hcons).toElementMap x ≤ z := by
  rintro Y' ⟨X', hX'x, hX'mem, hY'mem, hsub⟩
  have hzint : z.mem (interYs V₁.master L X') := by
    apply Element.mem_interYs_of
    intro p hp hX'p
    have hp1x : x.mem p.1 := x.up_mem hX'x (hL p hp).1 hX'p
    have hle : V₁.principal (hL p hp).2 ≤ z := hz _ ⟨p, hp, hp1x, rfl⟩
    exact hle p.2 ⟨(hL p hp).2, subset_rfl⟩
  exact z.up_mem hzint hY'mem hsub

end DomainTheory.Neighborhood
