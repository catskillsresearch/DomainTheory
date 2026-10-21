/-ai
The intersection of the sets presented by two lists of endpoint pairs equals the set presented by their pairwise combination.

A point of both unions lies in one interval from each list, hence in the interval whose left endpoint is the supremum of the two left endpoints and whose right endpoint is the infimum of the two right endpoints. Conversely, a point of such a combined interval lies in each of the two original intervals.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.Interval.Set.LinearOrder
import all Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Lattice.Bounded
import all Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
import all Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Algebra.Order.Field.Rat
import all Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.NormNum
import all Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Field.Basic
import all Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Card
import all Mathlib.Data.Fintype.Card
public import Mathlib.Order.CompleteLattice.Finset
import all Mathlib.Order.CompleteLattice.Finset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.presentedIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.mem_presentedIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.presentedIntervals_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.combineIntervals

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- **The presented family is closed under intersection**, with no side conditions on endpoints:
`Set.Ico_inter_Ico` handles crossed bounds automatically by returning the empty interval. -/
theorem presentedIntervals_inter (L1 L2 : List (ℚ × ℚ)) :
    presentedIntervals L1 ∩ presentedIntervals L2 = presentedIntervals (combineIntervals L1 L2) := by
  ext x
  simp only [mem_presentedIntervals, combineIntervals, List.mem_flatMap, List.mem_map,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨p, hp, hxp1, hxp2⟩, ⟨q, hq, hxq1, hxq2⟩⟩
    exact ⟨(p.1 ⊔ q.1, p.2 ⊓ q.2), ⟨p, hp, q, hq, rfl⟩, sup_le hxp1 hxq1, lt_inf_iff.mpr ⟨hxp2, hxq2⟩⟩
  · rintro ⟨r, ⟨p, hp, q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨p, hp, le_sup_left.trans hx1, hx2.trans_le inf_le_left⟩,
      ⟨q, hq, le_sup_right.trans hx1, hx2.trans_le inf_le_right⟩⟩

end DomainTheory.NeighbourhoodSystems
