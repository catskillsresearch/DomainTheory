/-ai
Subtracting one rational pair from a presenting list is the flat map of the one-pair difference over that list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffOneList

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **Subtract a single interval-pair `q` from a whole presenting list `L`.** -/
def diffSingleList (L : List (ℚ × ℚ)) (q : ℚ × ℚ) : List (ℚ × ℚ) :=
  L.flatMap (fun p => diffOneList p q)

end DomainTheory.NeighbourhoodSystems
