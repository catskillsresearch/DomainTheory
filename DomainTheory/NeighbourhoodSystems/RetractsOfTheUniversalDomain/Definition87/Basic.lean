/-ai
Clipping every endpoint pair of a presenting list to the half-open unit interval presents the intersection of the original union with that interval. Discarding pairs whose left endpoint fails to lie strictly below the right leaves the presented set unchanged. A set is a neighbourhood of the universal system if and only if it is nonempty and equal to the union presented by a list of intervals whose endpoints satisfy the bounds of Definition 8.7. Cutting every right endpoint at a rational presents the intersection with the open ray below that rational, and raising every left endpoint to a rational presents the intersection with the closed ray from that rational.

Each identity is proved by extensionality of membership. A point of a clipped interval lies in the original interval and in the clipping set, and a point of both is recovered by clipping its witnessing pair. A point of an interval forces the left endpoint strictly below the right, so the strictness filter keeps every witness. From a neighbourhood one clips the presenting list and discards the remaining degenerate pairs; the filter and clip identities, with the inclusion in the unit interval, recover the set, and each surviving pair meets the bounds. Conversely a bounded presenting list exhibits presentability and nonemptiness, and every point of such an interval lies in the unit interval by the endpoint inequalities.
ai-/
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

/-!
# Definition 8.7 (Scott 1981, PRG-19, Lecture VIII) — the universal domain `𝒰` over `ℚ`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Definition 8.7:

> Let `ℚ` be the set of rational numbers, and let `[0,1) = {q ∈ ℚ | 0 ≤ q < 1}`, and similarly for
> `[r,s)` for any `r < s` in `ℚ`. The neighbourhood system `𝒰` over `[0,1)` is the set of all
> non-empty finite unions of rational intervals `[r,s)` with `0 ≤ r < s ≤ 1`.

## Encoding

A finite union of intervals is coded by a `List (ℚ × ℚ)` of endpoint pairs
(`presentedIntervals L := ⋃ p ∈ L, Set.Ico p.1 p.2`). Rather than build the endpoint bounds
`0 ≤ r < s ≤ 1` into the *list* (which would force bookkeeping through every list operation), we
build `𝒰.mem X` from the *unconstrained* presentability of `X` plus the two set-level conditions
Scott's family actually cares about: `X` is non-empty and `X ⊆ [0,1)`. `mem_iff_scott` below shows
this is no relaxation at all: it is *equivalent* to Scott's literal per-pair-bounded description,
since clipping any presenting list to `[0,1)` and discarding degenerate (empty) pairs changes
neither the represented set nor its non-emptiness/inclusion in `[0,1)`.

The point of this encoding is that closure under intersection becomes endpoint-bookkeeping-free:
`Set.Ico_inter_Ico` says `Ico a₁ b₁ ∩ Ico a₂ b₂ = Ico (a₁ ⊔ a₂) (b₁ ⊓ b₂)` *unconditionally* (the
result is simply empty when the sup/inf bounds cross), so pairwise-combining two presenting lists
(`combineIntervals`) always presents the intersection, with no case split on validity.

## Axiom footprint

Every proof here is elementary finite-list recursion plus the linear order on `ℚ` — no genuine
appeal to choice is made. However, `#print axioms` reports `[propext, Classical.choice,
Quot.sound]` throughout, because the *pinned Mathlib's* bundled order instance for `ℚ`
(`Rat.instLinearOrder` in `Mathlib.Algebra.Order.Ring.Unbundled.Rat`) is itself
`Classical.choice`-tainted at the axiom level — even `Rat.le_refl` reports this footprint in this
Mathlib snapshot (confirmed directly, and also for the pre-existing `Exercise117.lean`, whose
`ratIntervalMem_nonempty` is likewise `Classical.choice`-tainted despite that file's now-stale
"choice-free" docstring claim). This is an upstream artifact of `ℚ`'s order hierarchy, not a
choice made in this file; nothing here uses `Classical.choice`, `Classical.dec`, or any
non-constructive existence principle directly.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-! ### Finite unions of rational intervals -/


/-! ### `𝒰`, the universal neighbourhood system over `[0,1) ⊆ ℚ` -/


/-! ### Faithfulness: `U.mem` literally matches Scott's per-pair-bounded description -/


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

/-! ### `𝒰` has no minimal neighbourhoods -/


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

/-! ### `𝒰` is closed under finite unions (needed for Theorem 8.8) -/
end DomainTheory.NeighbourhoodSystems
