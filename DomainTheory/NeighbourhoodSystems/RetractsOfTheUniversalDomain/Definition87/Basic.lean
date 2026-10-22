module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.CompleteLattice.Finset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.presentedIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.combineIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.UMem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.U
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.clip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.clipLt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.clipGe
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.mem_presentedIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.presentedIntervals_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.presentedIntervals_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.presentedIntervals_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.UMaster
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.U_master_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.UMaster_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.U_inter_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.U_sub_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.clip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.clipLt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.clipGe

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


theorem presentedIntervals_map_clip (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map clip) = presentedIntervals L ∩ Set.Ico (0 : ℚ) 1 := by
  ext x
  simp only [mem_presentedIntervals, List.mem_map, Set.mem_inter_iff, Set.mem_Ico, clip]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, le_sup_left.trans hx1, hx2.trans_le inf_le_left⟩,
      le_sup_right.trans hx1, hx2.trans_le inf_le_right⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hx0, hx1⟩
    exact ⟨(q.1 ⊔ 0, q.2 ⊓ 1), ⟨q, hq, rfl⟩, sup_le hxq1 hx0, lt_inf_iff.mpr ⟨hxq2, hx1⟩⟩

private theorem presentedIntervals_filter_lt (L : List (ℚ × ℚ)) :
    presentedIntervals (L.filter (fun p => decide (p.1 < p.2))) = presentedIntervals L := by
  ext x
  simp only [mem_presentedIntervals, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨hp, -⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx1, hx2⟩
    exact ⟨p, ⟨hp, lt_of_le_of_lt hx1 hx2⟩, hx1, hx2⟩

/-- **`U` really is Scott's literal family**: a set is a `U`-neighbourhood iff it is presentable
by a list of intervals `[r,s)` individually satisfying Scott's bounds `0 ≤ r < s ≤ 1`, and is
non-empty. Reconciles the bookkeeping-free encoding of `U` above with Definition 8.7 verbatim. -/
theorem U_mem_iff_scott {X : Set ℚ} :
    U.mem X ↔ ∃ L : List (ℚ × ℚ), (∀ p ∈ L, (0 : ℚ) ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1) ∧
      X = presentedIntervals L ∧ X.Nonempty := by
  constructor
  · rintro ⟨⟨L, rfl⟩, hne, hsub⟩
    refine ⟨(L.map clip).filter (fun p => decide (p.1 < p.2)), ?_, ?_, ?_⟩
    · rintro p hp
      obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp1
      exact ⟨le_sup_right, decide_eq_true_eq.mp hp2, inf_le_right⟩
    · rw [presentedIntervals_filter_lt, presentedIntervals_map_clip,
        Set.inter_eq_left.mpr hsub]
    · exact hne
  · rintro ⟨L, hbound, rfl, hne⟩
    refine ⟨⟨L, rfl⟩, hne, ?_⟩
    rintro x hx
    obtain ⟨p, hp, hx1, hx2⟩ := mem_presentedIntervals.mp hx
    obtain ⟨hp0, -, hp1⟩ := hbound p hp
    exact ⟨hp0.trans hx1, hx2.trans_le hp1⟩


theorem presentedIntervals_map_clipLt (m : ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map (clipLt m)) = presentedIntervals L ∩ Set.Iio m := by
  ext x
  simp only [mem_presentedIntervals, List.mem_map, Set.mem_inter_iff, Set.mem_Iio, clipLt]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, hx1, hx2.trans_le inf_le_left⟩, hx2.trans_le inf_le_right⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hxm⟩
    exact ⟨(q.1, q.2 ⊓ m), ⟨q, hq, rfl⟩, hxq1, lt_inf_iff.mpr ⟨hxq2, hxm⟩⟩

theorem presentedIntervals_map_clipGe (m : ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map (clipGe m)) = presentedIntervals L ∩ Set.Ici m := by
  ext x
  simp only [mem_presentedIntervals, List.mem_map, Set.mem_inter_iff, Set.mem_Ici, clipGe]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, le_sup_left.trans hx1, hx2⟩, le_sup_right.trans hx1⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hxm⟩
    exact ⟨(q.1 ⊔ m, q.2), ⟨q, hq, rfl⟩, sup_le hxq1 hxm, hxq2⟩

end DomainTheory.NeighbourhoodSystems
