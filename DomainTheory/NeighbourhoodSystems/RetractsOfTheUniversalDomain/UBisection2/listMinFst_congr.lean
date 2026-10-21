/-ai
Two nonempty, nondegenerate, unit-interval-bounded presenting lists of the same set of intervals have the same minimum first component.

Each minimum lies in the other presented set, by membership of the minimum in its own presented intervals and the equality of the two presented sets. Each minimum is then at most the other by the lower bound, so the two minima are equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst_mem_presentedIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMinFst_lower_bound

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`listMinFst` is a well-defined function of the presented set alone**, mirroring
`MinLevel.lean`'s `minLevel_unique` for `V`: two (nonempty, nondegenerate, `[0,1]`-bounded)
presenting lists of the *same* set have the same `listMinFst`. -/
theorem listMinFst_congr {L1 L2 : List (ℚ × ℚ)} (hne1 : L1 ≠ []) (hne2 : L2 ≠ [])
    (hpos1 : ∀ p ∈ L1, p.1 < p.2) (hb1 : ∀ p ∈ L1, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (hpos2 : ∀ p ∈ L2, p.1 < p.2) (hb2 : ∀ p ∈ L2, 0 ≤ p.1 ∧ p.2 ≤ 1)
    (heq : presentedIntervals L1 = presentedIntervals L2) :
    listMinFst L1 = listMinFst L2 := by
  have hm1 : listMinFst L1 ∈ presentedIntervals L2 :=
    heq ▸ listMinFst_mem_presentedIntervals hne1 hpos1 hb1
  have hm2 : listMinFst L2 ∈ presentedIntervals L1 :=
    heq ▸ listMinFst_mem_presentedIntervals hne2 hpos2 hb2
  exact le_antisymm (listMinFst_lower_bound hm2) (listMinFst_lower_bound hm1)

end DomainTheory.NeighbourhoodSystems
