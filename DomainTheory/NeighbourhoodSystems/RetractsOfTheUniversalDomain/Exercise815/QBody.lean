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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal

variable (r : ℕ → ℕ)

/-- One fuel-recursion step for evaluating a term-algebra code: tag `0` (`leaf j`) applies `r` to
the payload; tag `1` (`node t1 t2`) combines the two (previous-fuel-level) recursive values via
`Uinter`; any other tag (`master`, or junk) falls back to `𝒰`'s master index. Mirrors
`decodeFuelOkCharBody`'s tag-dispatch shape exactly. -/
def QBody (prev : ℕ → ℕ) (c : ℕ) : ℕ :=
  selectFn (isOne (1 - c.unpair.1)) (r c.unpair.2)
    (selectFn (isOne (2 - c.unpair.1))
      (Uinter (prev c.unpair.2.unpair.1) (prev c.unpair.2.unpair.2))
      UComputablePresentation.masterIdx)

end TreeVal

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
