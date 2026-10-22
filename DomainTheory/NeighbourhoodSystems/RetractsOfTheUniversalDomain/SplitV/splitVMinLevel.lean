module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- The presentation-independent canonical level of `VX n`. -/
def splitVMinLevel (n : ℕ) : ℕ := minLevel (canonIdx n).unpair.1 (canonIdx n).unpair.2

end DomainTheory.NeighbourhoodSystems
