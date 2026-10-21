/-ai
The union of a nonempty chain of elements of a domain lies below every upper bound of the chain.

A neighbourhood of the union belongs to some member of the chain, and that member lies below the upper bound, so the neighbourhood belongs to the upper bound.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise124
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise415.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- `chainUnion C` is the least upper bound of the chain: an upper bound `y` of every member
dominates it. -/
theorem chainUnion_le (C : Set V.Element) (hne : C.Nonempty) (hchain : IsChain (· ≤ ·) C)
    {y : V.Element} (hy : ∀ x ∈ C, x ≤ y) : V.chainUnion C hne hchain ≤ y := by
  rintro Z ⟨x, hxC, hxZ⟩
  exact hy x hxC Z hxZ

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
