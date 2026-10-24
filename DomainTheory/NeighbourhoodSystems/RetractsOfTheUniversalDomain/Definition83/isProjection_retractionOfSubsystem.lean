module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.IsProjection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.IsFinitary
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.FinitaryProjection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.retractionOfSubsystem_le_idMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {D E : NeighborhoodSystem α}


namespace Subsystem

variable {h : D ◁ E}

/-- **Every `retractionOfSubsystem h` is a projection** (Definition 8.3). -/
theorem isProjection_retractionOfSubsystem (h : D ◁ E) :
    IsProjection (retractionOfSubsystem h) :=
  ⟨isRetraction_retractionOfSubsystem h, retractionOfSubsystem_le_idMap h⟩

end Subsystem
end DomainTheory.NeighbourhoodSystems
