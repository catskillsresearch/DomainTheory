module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.leastMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Scott's Proposition 3.9: under consistency of a finite step list, the least map lies in the
    step function, is minimal among maps in that neighbourhood, and containment of the step
    function in a step is equivalent to containment of the associated range intersection. -/
theorem proposition_3_9 :
    (∀ {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
      (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)),
      leastMap L hL hcons ∈ stepFun L) ∧
    (∀ {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
      (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X))
      {f : ApproximableMap V₀ V₁}, f ∈ stepFun L → leastMap L hL hcons ≤ f) ∧
    (∀ {L : List (Set α × Set β)} (_hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
      (_hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X))
      {X : Set α} {Y : Set β} (_hX : V₀.mem X) (_hY : V₁.mem Y),
      (stepFun L : Set (ApproximableMap V₀ V₁)) ⊆ step X Y ↔
        interYs V₁.master L X ⊆ Y) :=
  ⟨leastMap_mem_stepFun, leastMap_le, stepFun_subset_step_iff⟩

end DomainTheory.NeighbourhoodSystems
