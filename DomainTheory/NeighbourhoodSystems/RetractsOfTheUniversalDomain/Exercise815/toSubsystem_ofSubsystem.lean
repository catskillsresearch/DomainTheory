module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.ofSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.toSubsystem_ofSubsystem_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section OrderIso

variable (P : ComputablePresentation D)

/-- **Round trip 1.** `toSubsystem P (ofSubsystem P D' hD') = ⟨D', hD'⟩`. -/
theorem toSubsystem_ofSubsystem (D' : NeighborhoodSystem α) (hD' : D' ◁ D) :
    toSubsystem P (ofSubsystem P D' hD') = ⟨D', hD'⟩ :=
  Subtype.ext (NeighborhoodSystem.ext (toSubsystem_ofSubsystem_mem P D' hD') hD'.master_eq.symm)

end OrderIso

end DomainTheory.NeighbourhoodSystems
