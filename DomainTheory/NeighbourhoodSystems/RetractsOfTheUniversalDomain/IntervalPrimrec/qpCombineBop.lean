/-ai
The rational-pair combine operation sends a code of two rational pairs to the code of
the pair whose first component is the maximum of the two first components and whose
second component is the minimum of the two second components, realizing the pointwise
combination of the corresponding intervals.
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

/-- The per-pair-code operation `(pc, qc) ↦ (max, min)` realizing `(p.1 ⊔ q.1, p.2 ⊓ q.2)`. -/
def qpCombineBop (t : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair t.unpair.1.unpair.1 t.unpair.2.unpair.1))
    (ratMinCode (Nat.pair t.unpair.1.unpair.2 t.unpair.2.unpair.2))

end DomainTheory.NeighbourhoodSystems
