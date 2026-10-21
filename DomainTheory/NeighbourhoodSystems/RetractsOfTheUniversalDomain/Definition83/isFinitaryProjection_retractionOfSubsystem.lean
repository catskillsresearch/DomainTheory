/-ai
The retraction of a subsystem is a finitary projection.

The proof pairs the fact that this retraction is a projection with the fact that it is finitary.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.isProjection_retractionOfSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.isFinitary_retractionOfSubsystem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {D E : NeighborhoodSystem α}




namespace Subsystem

variable {h : D ◁ E}

/-- **Every `retractionOfSubsystem h` is a finitary projection** (Definition 8.3, both clauses). -/
theorem isFinitaryProjection_retractionOfSubsystem (h : D ◁ E) :
    IsFinitaryProjection (retractionOfSubsystem h) :=
  ⟨isProjection_retractionOfSubsystem h, isFinitary_retractionOfSubsystem h⟩

end Subsystem
end DomainTheory.NeighbourhoodSystems
