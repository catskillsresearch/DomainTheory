/-ai
Each active principal filter, for a pair whose input belongs to the element, lies below the least map at that element.

The output of the pair belongs to the least map at the element, because the input belongs to the element and the least map lies in the step neighborhood of the pair. Every neighborhood of the principal filter is then a neighborhood of the least map at the element by upward closure.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise328.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- Each active value `↑Yᵢ` (with `Xᵢ ∈ x`) approximates `f₀(x)`, because `Yᵢ ∈ f₀(x)`. -/
theorem val_le_leastMap_toElementMap {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {x : V₀.Element}
    {p : Set α × Set β} (hp : p ∈ L) (hp1x : x.mem p.1) :
    V₁.principal (hL p hp).2 ≤ (leastMap L hL hcons).toElementMap x := by
  have hmem : ((leastMap L hL hcons).toElementMap x).mem p.2 :=
    ⟨p.1, hp1x, leastMap_mem_stepFun hL hcons p hp⟩
  intro Z hZ
  exact ((leastMap L hL hcons).toElementMap x).up_mem hmem hZ.1 hZ.2

end DomainTheory.NeighbourhoodSystems
