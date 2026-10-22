module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- The `{0,1}` flag: does the rational-pair code `e` decode to a non-degenerate pair `p.1 < p.2`? -/
def qpNonemptyBop (e : ℕ) : ℕ := ratLtCode (Nat.pair e.unpair.1 e.unpair.2)

end DomainTheory.NeighbourhoodSystems
