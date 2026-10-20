module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffOneCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- `diffSingleCode accL q` subtracts the single interval-pair coded by `q` from the whole
QPair-list coded by `accL`. -/
def diffSingleCode (accL q : ℕ) : ℕ := flatMapCode diffOneCode q accL

end DomainTheory.NeighbourhoodSystems
