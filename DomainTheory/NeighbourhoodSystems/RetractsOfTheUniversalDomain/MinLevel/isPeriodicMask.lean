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
