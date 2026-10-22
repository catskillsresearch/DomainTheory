module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise213
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.Basic

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.fixedNbhd_subsystem
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}


/-- **The easy half of Theorem 8.6's range characterization.** If `f` is a fixed point of `sub`,
then `f` is a finitary projection: `sub f = f` says exactly that `f` *is*
`retractionOfSubsystem (fixedNbhd_subsystem f)`, and Definition 8.3's corollary of Proposition 8.2
finishes immediately. (The converse — every finitary projection is a fixed point of `sub` — is
Theorem 8.5's harder direction; see the module docstring.) -/
theorem isFinitaryProjection_of_sub_eq_self {f : ApproximableMap E E} (h : sub f = f) :
    FinitaryProjection f := by
  rw [← h]
  exact Subsystem.isFinitaryProjection_retractionOfSubsystem (fixedNbhd_subsystem f)

end DomainTheory.NeighbourhoodSystems
