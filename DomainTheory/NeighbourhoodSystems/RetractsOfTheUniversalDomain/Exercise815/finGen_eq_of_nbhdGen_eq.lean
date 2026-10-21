/-ai
If two finite index lists determine the same principal up-set, they generate the same finitely generated subsystem.

Each list belongs to its own up-set, so equality of the up-sets puts each list in the other's up-set, and the two inclusions give equality of the generated subsystems.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.self_mem_nbhdGen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section SubD

variable (P : ComputablePresentation D)

/-- **Injectivity of `nbhd` on `Fin`.** `nbhd(a) = nbhd(b) → Fin(a) = Fin(b)`: evaluate the set
equality at `a` and at `b` (both reflexively self-membership) and combine by antisymmetry. -/
theorem finGen_eq_of_nbhdGen_eq {a b : List ℕ} (h : nbhdGen P a = nbhdGen P b) :
    finGen P a = finGen P b :=
  Set.Subset.antisymm ((Set.ext_iff.mp h b).mpr (self_mem_nbhdGen P b))
    ((Set.ext_iff.mp h a).mp (self_mem_nbhdGen P a))

end SubD

end DomainTheory.NeighbourhoodSystems
