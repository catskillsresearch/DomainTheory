module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- Decode a natural as a list of rational pairs. -/
def decodeQPairList (c : ℕ) : List (ℚ × ℚ) := (decodeList c).map decodeRatPair

end DomainTheory.NeighbourhoodSystems
