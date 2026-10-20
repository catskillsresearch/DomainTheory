module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.splitU2MidCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The "left" half of the canonical split of `Xₙ`: `Xₙ ∩ (-∞, m)` for `m` the midpoint of `Xₙ`'s
intrinsic `(min, max)`. -/
def splitU2Left (n : ℕ) : ℕ := clipLtListCode (splitU2MidCode n) (canonCode n)

end DomainTheory.NeighbourhoodSystems
