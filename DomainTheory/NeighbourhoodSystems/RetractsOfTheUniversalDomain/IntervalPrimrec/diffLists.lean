/-ai
Subtracting one presenting list of rational pairs from another is the flat map that subtracts the second list from each pair of the first.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffAllList

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **Subtract `L2` from `L1`**, presenting the set difference `presentedIntervals L1 \\
presentedIntervals L2`. -/
def diffLists (L1 L2 : List (ℚ × ℚ)) : List (ℚ × ℚ) := L1.flatMap (fun p => diffAllList p L2)

end DomainTheory.NeighbourhoodSystems
