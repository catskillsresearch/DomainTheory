module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.lowerSet
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.upperSet
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.mem_lowerSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair


@[simp] theorem mem_upperSet (P : ProjectionPair D E) {x : D.Element} {y : E.Element} :
    y ∈ P.upperSet x ↔ x ≤ P.proj.toElementMap y := Iff.rfl

end Subsystem.ProjectionPair
end DomainTheory.NeighbourhoodSystems
