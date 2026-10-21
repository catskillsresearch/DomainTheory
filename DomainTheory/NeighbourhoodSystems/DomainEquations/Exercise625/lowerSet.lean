/-ai
The lower set of an element y is the set of elements x such that the injection of x lies below y.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- The set `{x ∈ |𝒟| ∣ g(x) ⊑ y}` of the first formula. By the Galois connection it is the
down-set `{x ∣ x ⊑ h(y)}` of `h(y)`. -/
def lowerSet (P : ProjectionPair D E) (y : E.Element) : Set D.Element :=
  {x | P.inj.toElementMap x ≤ y}

end Subsystem.ProjectionPair

end DomainTheory.NeighbourhoodSystems
