module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep_iter_levelSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_myModPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsample

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`myUpsample` realizes `upsample` at the `levelSet` level.** -/
theorem levelSet_myUpsample {k k' : ℕ} (hk : k ≤ k') (m : ℕ) :
    levelSet k' (myUpsample k k' m) = levelSet k m := by
  unfold myUpsample
  rw [levelSet_myModPow2]
  have := myUpsampleJointStep_iter_levelSet k m (k' - k)
  rwa [show k + (k' - k) = k' from by omega] at this

end DomainTheory.NeighbourhoodSystems
