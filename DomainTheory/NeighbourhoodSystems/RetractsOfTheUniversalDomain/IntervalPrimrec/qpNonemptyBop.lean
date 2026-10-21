/-ai
The nonemptiness flag of a rational-pair code is the value in {0, 1} recording whether
the code decodes to a nondegenerate pair, that is, whether the first component is
strictly less than the second. It is the strict comparison of the two components of the
code.
ai-/
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
