module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.fixedNbhd_retractionOfSubsystem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- Every `retractionOfSubsystem h` is already a fixed point of `sub` — immediate from the round
trip `fixedNbhd_retractionOfSubsystem`, since `sub` is *defined* as `retractionOfSubsystem` applied
to `fixedNbhd`. -/
theorem sub_retractionOfSubsystem {D : NeighborhoodSystem α} (h : D ◁ E) :
    sub (Subsystem.retractionOfSubsystem h) = Subsystem.retractionOfSubsystem h := by
  unfold sub
  congr 1
  exact fixedNbhd_retractionOfSubsystem h

end DomainTheory.NeighbourhoodSystems
