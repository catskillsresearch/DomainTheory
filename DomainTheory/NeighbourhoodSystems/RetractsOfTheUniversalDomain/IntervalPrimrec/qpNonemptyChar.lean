module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.qpNonemptyBop

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- The `{0,1}` flag: does the QPair-list code `c` present a non-empty set? A bounded `∃` over
`decodeList c` via `Recursive.lean`'s `existsListChar` (the second argument of `existsListChar` is
an unused parameter, fixed to `0`). -/
def qpNonemptyChar (c : ℕ) : ℕ := existsListChar (fun t => qpNonemptyBop t.unpair.1) 0 c

end DomainTheory.NeighbourhoodSystems
