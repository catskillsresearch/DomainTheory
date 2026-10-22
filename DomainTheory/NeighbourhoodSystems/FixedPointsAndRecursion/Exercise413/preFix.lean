module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- The set of *pre-fixed points* `{x ∣ f(x) ⊑ x}` of `f`. -/
def preFix (f : V.Element → V.Element) : Set V.Element := {x | f x ≤ x}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
