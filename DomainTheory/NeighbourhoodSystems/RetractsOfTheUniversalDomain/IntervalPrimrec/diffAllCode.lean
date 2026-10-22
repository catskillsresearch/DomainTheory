module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffAllStep

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- `diffAllCode pc L2` subtracts the whole QPair-list coded by `L2` from the single interval-pair
coded by `pc`, folding `diffSingleCode` over `L2` from the seed `[pc]`. -/
def diffAllCode (pc L2 : ℕ) : ℕ := foldCode diffAllStep 0 (Nat.pair pc 0 + 1) L2

end DomainTheory.NeighbourhoodSystems
