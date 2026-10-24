module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.IsProjection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.IsFinitary
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.FinitaryProjection

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {D E : NeighborhoodSystem α}


namespace Subsystem

variable {h : D ◁ E}

/-- **Every `retractionOfSubsystem h` is finitary** (Definition 8.3): its fixed-point set is
isomorphic to `|D|` itself, by Proposition 8.2's `elementIso`. -/
theorem isFinitary_retractionOfSubsystem (h : D ◁ E) :
    IsFinitary (retractionOfSubsystem h) :=
  ⟨α, D, ⟨(elementIso h).symm⟩⟩

end Subsystem
end DomainTheory.NeighbourhoodSystems
