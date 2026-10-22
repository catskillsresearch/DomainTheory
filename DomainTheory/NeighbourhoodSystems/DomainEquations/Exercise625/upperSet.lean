module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.mem_lowerSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- The set `{y ∈ |ℰ| ∣ x ⊑ h(y)}` of the second formula. By the Galois connection it is the
up-set `{y ∣ g(x) ⊑ y}` of `g(x)`. -/
def upperSet (P : ProjectionPair D E) (x : D.Element) : Set E.Element :=
  {y | x ≤ P.proj.toElementMap y}

end Subsystem.ProjectionPair

end DomainTheory.NeighbourhoodSystems
