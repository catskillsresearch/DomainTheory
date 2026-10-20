module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt_encodeInt

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- Decode a natural code as a rational via `mkRat`: `pair c d ↦ mkRat (decodeInt c) (d + 1)`. -/
def decodeRat (c : ℕ) : ℚ := mkRat (decodeInt c.unpair.1) (c.unpair.2 + 1)

end DomainTheory.NeighbourhoodSystems
