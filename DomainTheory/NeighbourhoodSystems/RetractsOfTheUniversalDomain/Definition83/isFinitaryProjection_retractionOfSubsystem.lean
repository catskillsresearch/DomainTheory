module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.IsProjection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.IsFinitary
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.FinitaryProjection
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
    FinitaryProjection (retractionOfSubsystem h) :=
  ⟨⟨isProjection_retractionOfSubsystem h, isFinitary_retractionOfSubsystem h⟩⟩

end Subsystem
end DomainTheory.NeighbourhoodSystems
