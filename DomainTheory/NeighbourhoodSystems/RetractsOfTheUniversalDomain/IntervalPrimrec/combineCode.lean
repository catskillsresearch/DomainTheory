/-ai
The combination code of two natural codes is the cross combination, by the pair-combination operation, of those codes.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.qpCombineBop

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- `combineCode` realizes `combineIntervals` on codes: `Nat.Primrec` in both arguments. -/
def combineCode (c1 c2 : ℕ) : ℕ := crossCombine qpCombineBop c1 c2

end DomainTheory.NeighbourhoodSystems
