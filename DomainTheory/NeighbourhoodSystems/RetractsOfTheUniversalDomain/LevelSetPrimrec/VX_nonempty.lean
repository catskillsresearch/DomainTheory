module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_canonIdx_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.VX

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem VX_nonempty (c : ℕ) : (VX c).Nonempty := levelSet_canonIdx_nonempty c

end DomainTheory.NeighbourhoodSystems
