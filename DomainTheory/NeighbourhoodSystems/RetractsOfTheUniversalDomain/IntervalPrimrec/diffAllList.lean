/-ai
Subtracting a list of rational pairs from a single pair is the fold of the single-list difference over that list, starting from the singleton list of the pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffSingleList

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **Subtract a whole presenting list `L2` from a single interval-pair `p`**, by folding
`diffSingleList` over `L2`, starting from `[p]`. -/
def diffAllList (p : ℚ × ℚ) (L2 : List (ℚ × ℚ)) : List (ℚ × ℚ) := L2.foldl diffSingleList [p]

end DomainTheory.NeighbourhoodSystems
