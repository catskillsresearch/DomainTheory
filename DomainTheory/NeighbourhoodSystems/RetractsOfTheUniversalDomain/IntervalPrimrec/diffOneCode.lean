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
