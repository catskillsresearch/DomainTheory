/-ai
The set of pre-fixed points of an endomap f of the elements is the set of elements x such that f(x) lies below x.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- The set of *pre-fixed points* `{x ∣ f(x) ⊑ x}` of `f`. -/
def preFix (f : V.Element → V.Element) : Set V.Element := {x | f x ≤ x}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
