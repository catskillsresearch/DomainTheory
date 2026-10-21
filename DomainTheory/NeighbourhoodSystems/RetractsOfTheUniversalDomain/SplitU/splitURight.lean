/-ai
splitURight n is the right half of the canonical split of the neighbourhood of n: every pair of its canonical presenting list, clipped into the closed ray from the midpoint of the first pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.clipGeListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.splitMidCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The "right" half of the canonical split of `Xₙ`: `Xₙ ∩ [m, ∞)`. -/
def splitURight (n : ℕ) : ℕ := clipGeListCode (splitMidCode n) (canonCode n)

end DomainTheory.NeighbourhoodSystems
