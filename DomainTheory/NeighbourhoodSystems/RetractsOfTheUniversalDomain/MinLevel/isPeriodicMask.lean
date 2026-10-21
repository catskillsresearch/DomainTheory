/-ai
The periodicity test of a level, a candidate smaller level, and a mask is the zero-test of the two-sided truncated difference between the upsample, from the candidate level to the original level, of the mask truncated at two to the candidate level, and the mask truncated at two to the original level. For a candidate at most the original level it decides whether the level set is also presentable at the candidate level through the mask's own bits.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **`isPeriodicMask k j m ∈ {0,1}`** decides whether `levelSet k m` is also presentable at level
`j` via `m`'s own low bits (`isPeriodicMask_iff`), for `j ≤ k`. Meaningless (junk) for `j > k`,
exactly like `myUpsample` itself. -/
def isPeriodicMask (k j m : ℕ) : ℕ :=
  isZero ((myUpsample j k (myModPow2 m (2 ^ j)) - myModPow2 m (2 ^ k)) +
    (myModPow2 m (2 ^ k) - myUpsample j k (myModPow2 m (2 ^ j))))

end DomainTheory.NeighbourhoodSystems
