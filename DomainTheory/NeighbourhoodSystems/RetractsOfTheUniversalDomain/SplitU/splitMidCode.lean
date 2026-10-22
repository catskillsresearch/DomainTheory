module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.firstElemCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The midpoint code of the first pair of `canonCode n`'s presenting list. -/
def splitMidCode (n : ℕ) : ℕ := ratMidCode (firstElemCode (canonCode n))

end DomainTheory.NeighbourhoodSystems
