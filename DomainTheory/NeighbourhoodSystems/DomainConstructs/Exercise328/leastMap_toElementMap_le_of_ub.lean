/-ai
Any upper bound of the active values at an element lies above the least map at that element.

A neighborhood of the least map at the element comes from an input belonging to the element together with a superset of the finite intersection of the relevant outputs. That intersection belongs to the upper bound, because each relevant output has its principal filter among the active values and hence below the upper bound, so the output itself belongs to the upper bound. The original neighborhood then belongs to the upper bound by upward closure.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise328.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise328.Elementu2emem_interYs_of

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

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

end DomainTheory.NeighbourhoodSystems
