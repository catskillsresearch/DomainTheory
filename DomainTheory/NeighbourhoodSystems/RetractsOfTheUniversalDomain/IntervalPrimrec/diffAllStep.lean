module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffSingleCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- `foldCode`'s step for `diffAllCode`'s fold over `L2` (params unused): pops `q`, subtracts it
from the "remaining pieces" accumulator via `diffSingleCode`. -/
def diffAllStep (w : ℕ) : ℕ := diffSingleCode w.unpair.2.unpair.1 w.unpair.1

end DomainTheory.NeighbourhoodSystems
