module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.fixedNbhd_sub

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}


/-- **`sub` is idempotent: `sub (sub f) = sub f`** (sharper than Scott's stated `sub(f) ⊆
sub(sub(f))`, Theorem 8.6's projection clause for `sub` itself). Both sides are
`retractionOfSubsystem` of the *same* subsystem `fixedNbhd f` (`fixedNbhd_sub`), so they coincide
as maps, not merely as an inclusion. -/
theorem sub_sub (f : ApproximableMap E E) : sub (sub f) = sub f := by
  unfold sub
  congr 1
  exact fixedNbhd_sub f

end DomainTheory.NeighbourhoodSystems
