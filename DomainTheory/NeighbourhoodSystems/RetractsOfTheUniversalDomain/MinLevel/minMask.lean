module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel.minLevel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **`minMask k m`**: `m`'s own bits, truncated to `minLevel k m`'s width — the presentation-
independent canonical mask of the set `levelSet k m` (`minLevel_unique`). -/
def minMask (k m : ℕ) : ℕ := myModPow2 m (2 ^ minLevel k m)

end DomainTheory.NeighbourhoodSystems
