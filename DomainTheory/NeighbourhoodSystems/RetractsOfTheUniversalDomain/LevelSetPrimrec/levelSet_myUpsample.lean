/-ai
Upsampling a mask from level k to a level at least k presents, at the higher level, the
same set as the original mask at level k.

Unfolding upsampling, the final truncation does not change the level set. The iteration
of the joint step for the difference of the levels preserves the level set, and adding
that difference back to k recovers the higher level.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep_iter_levelSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_myModPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsample

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.V_no_minimal
@[expose] public section

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
