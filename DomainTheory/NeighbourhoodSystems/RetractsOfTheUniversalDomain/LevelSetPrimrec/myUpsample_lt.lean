module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsample

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`myUpsample` is always bounded** by `2 ^ (2 ^ k')`, regardless of whether a genuine
upsampling step occurs. -/
theorem myUpsample_lt (k k' m : ℕ) : myUpsample k k' m < 2 ^ (2 ^ k') := myModPow2_lt _ _

end DomainTheory.NeighbourhoodSystems
