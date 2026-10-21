/-ai
splitULeft n is the left half of the canonical split of the neighbourhood of n: every pair of its canonical presenting list, clipped into the open ray below the midpoint of the first pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.clipLtListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitMidCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The "left" half of the canonical split of `Xₙ`: `Xₙ ∩ (-∞, m)` for `m` the midpoint of `Xₙ`'s
first presenting pair. -/
def splitULeft (n : ℕ) : ℕ := clipLtListCode (splitMidCode n) (canonCode n)

end DomainTheory.NeighbourhoodSystems
