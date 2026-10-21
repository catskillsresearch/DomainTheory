/-ai
The code that subtracts the rational-pair list coded by one natural from the single pair coded by another is the fold of the difference step, starting from the code of the singleton list of that pair, over the subtracted list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffAllStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- `diffAllCode pc L2` subtracts the whole QPair-list coded by `L2` from the single interval-pair
coded by `pc`, folding `diffSingleCode` over `L2` from the seed `[pc]`. -/
def diffAllCode (pc L2 : ℕ) : ℕ := foldCode diffAllStep 0 (Nat.pair pc 0 + 1) L2

end DomainTheory.NeighbourhoodSystems
