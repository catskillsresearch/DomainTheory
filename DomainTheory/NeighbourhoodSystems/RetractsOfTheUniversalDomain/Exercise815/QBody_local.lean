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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QBody

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal

variable (r : ℕ → ℕ)

/-- `QBody`'s value at `c` depends on `prev` only through its values at `c`'s two (`Nat.unpair`)
children — the locality fact needed to bridge two different `prev`s that merely *agree* there. -/
theorem QBody_local (f g : ℕ → ℕ) (c : ℕ)
    (h1 : f c.unpair.2.unpair.1 = g c.unpair.2.unpair.1)
    (h2 : f c.unpair.2.unpair.2 = g c.unpair.2.unpair.2) :
    QBody r f c = QBody r g c := by
  unfold QBody
  rw [h1, h2]

end TreeVal

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
