/-ai
splitMidCode n is the code of the midpoint of the first rational pair in the presenting list of the canonical code of n.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.firstElemCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The midpoint code of the first pair of `canonCode n`'s presenting list. -/
def splitMidCode (n : ℕ) : ℕ := ratMidCode (firstElemCode (canonCode n))

end DomainTheory.NeighbourhoodSystems
