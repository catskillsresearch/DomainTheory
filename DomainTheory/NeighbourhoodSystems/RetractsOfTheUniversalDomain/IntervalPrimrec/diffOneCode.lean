/-ai
The code of a one-pair difference, from a natural whose unpaired components are the subtracted pair and the original pair, is the list code of the two endpoint combinations given by the rational minimum of the original right endpoint with the subtracted left endpoint and the rational maximum of the original left endpoint with the subtracted right endpoint.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- Code-level `diffOneList`, taking `t = pair qc pc` (subtracted interval `q` **first**, matching
`flatMapCode`'s calling convention). -/
def diffOneCode (t : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1.unpair.1)))
    (Nat.pair (Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2))
      t.unpair.2.unpair.2) 0 + 1) + 1

end DomainTheory.NeighbourhoodSystems
