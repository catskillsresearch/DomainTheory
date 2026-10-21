/-ai
Two level sets are equal if and only if the masks obtained by upsampling each to the
maximum of the two levels are equal.

If the level sets are equal, injectivity on masks strictly below the corresponding power
of two, the bound on upsampling, and preservation of the level set under upsampling to
each side of the maximum give equality of the upsampled masks. Conversely, rewriting
each level set by that preservation, equal upsampled masks present equal level sets.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsample
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_myUpsample
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsample_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.levelSet_inj_of_lt

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`levelSet` equality reduces to `myUpsample` equality** at the common level `max k₁ k₂`: this
is the injectivity criterion (`levelSet_inj_of_lt`) driving Scott's relation 7.1(i) decider. -/
theorem levelSet_eq_iff_myUpsample_eq (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 = levelSet k2 m2 ↔
      myUpsample k1 (max k1 k2) m1 = myUpsample k2 (max k1 k2) m2 := by
  constructor
  · intro h
    exact levelSet_inj_of_lt (myUpsample_lt _ _ _) (myUpsample_lt _ _ _)
      (by rw [levelSet_myUpsample (Nat.le_max_left k1 k2),
        levelSet_myUpsample (Nat.le_max_right k1 k2), h])
  · intro h
    rw [← levelSet_myUpsample (Nat.le_max_left k1 k2) m1,
      ← levelSet_myUpsample (Nat.le_max_right k1 k2) m2, h]

end DomainTheory.NeighbourhoodSystems
