module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- The presentation-independent canonical mask of `VX n`, at `splitVMinLevel n`'s width. -/
def splitVMinMask (n : ℕ) : ℕ := minMask (canonIdx n).unpair.1 (canonIdx n).unpair.2

end DomainTheory.NeighbourhoodSystems
