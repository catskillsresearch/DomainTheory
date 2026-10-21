/-ai
The right-hand code of the canonical split of the neighbourhood indexed by n is that neighbourhood clipped at and above the midpoint of its intrinsic minimum and maximum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The "right" half of the canonical split of `Xₙ`: `Xₙ ∩ [m, ∞)`. -/
def splitU2Right (n : ℕ) : ℕ := clipGeListCode (splitU2MidCode n) (canonCode n)

end DomainTheory.NeighbourhoodSystems
