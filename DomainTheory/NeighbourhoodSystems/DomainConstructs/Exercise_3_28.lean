module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.leastStepMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

/-- Scott's Exercise 3.28: the least map acts by a pointwise supremum of principals. -/
theorem example_328 :
    ∀ {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
      (L : List (Set α × Set β)) (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
      (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) (x : V₀.Element),
      (leastMap L hL hcons).toElementMap x
        = V₁.sSup (leastMapVals L hL x) (leastMapVals_bounded hL hcons x) :=
  @toElementMap_leastMap_eq_sSup

end DomainTheory.NeighbourhoodSystems
