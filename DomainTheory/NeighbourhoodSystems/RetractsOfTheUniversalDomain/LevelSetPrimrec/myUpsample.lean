/-ai
The computable re-expression of a level-k mask at a level k' is the truncation, to the
low two-to-the-k' bits, of the mask component obtained by iterating the joint upsampling
step, a number of times equal to k' minus k, from the pair of k and the mask. When k' is
at least k this agrees at the level-set level with upsampling and is bounded; the final
truncation does not change the presented set, but it supplies the bound when the two
levels are equal and the iteration takes no steps. When k' is strictly below k the
returned value is junk.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myUpsampleJointStep

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`myUpsample k k' m`**: the computable re-expression of a level-`k` mask `m` at level
`k' ≥ k`, agreeing with `Exercise812.lean`'s (non-computable) `upsample` at the `levelSet` level
(`levelSet_myUpsample`), and always *bounded* (`myUpsample_lt`) — the final `myModPow2` truncation
is a no-op mathematically (`levelSet_myModPow2`) but is essential to guarantee boundedness in the
degenerate `k = k'` case, where the raw iteration runs zero steps and would otherwise return `m`
unchanged (junk bits included). Undefined behaviour (returns junk) when `k' < k`. -/
def myUpsample (k k' m : ℕ) : ℕ :=
  myModPow2 ((myUpsampleJointStep^[k' - k] (Nat.pair k m)).unpair.2) (2 ^ k')

end DomainTheory.NeighbourhoodSystems
