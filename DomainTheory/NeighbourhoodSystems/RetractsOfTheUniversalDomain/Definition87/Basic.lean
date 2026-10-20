/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
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

namespace DomainTheory.Neighborhood

open NeighborhoodSystem

/-! ### Finite unions of rational intervals -/

/-- The set presented by a list of interval endpoint-pairs: the union `⋃ (r,s) ∈ L, [r,s)`. -/
def presentedIntervals (L : List (ℚ × ℚ)) : Set ℚ := ⋃ p ∈ L, Set.Ico p.1 p.2

@[simp] theorem mem_presentedIntervals {L : List (ℚ × ℚ)} {x : ℚ} :
    x ∈ presentedIntervals L ↔ ∃ p ∈ L, p.1 ≤ x ∧ x < p.2 := by
  simp only [presentedIntervals, Set.mem_iUnion, Set.mem_Ico, exists_prop]

@[simp] theorem presentedIntervals_nil : presentedIntervals ([] : List (ℚ × ℚ)) = ∅ := by
  ext x; simp

theorem presentedIntervals_cons (p : ℚ × ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (p :: L) = Set.Ico p.1 p.2 ∪ presentedIntervals L := by
  ext x; simp [Set.mem_Ico, or_and_right, exists_or]

/-- Pairwise-combine two endpoint-lists via `Set.Ico_inter_Ico`, realizing the intersection of the
two presented unions as another presented union. -/
def combineIntervals (L1 L2 : List (ℚ × ℚ)) : List (ℚ × ℚ) :=
  L1.flatMap (fun p => L2.map (fun q => (p.1 ⊔ q.1, p.2 ⊓ q.2)))

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

/-! ### `𝒰`, the universal neighbourhood system over `[0,1) ⊆ ℚ` -/

/-- Membership in Scott's universal family: non-empty subsets of `[0,1)` presentable as a
finite union of rational half-open intervals. -/
def UMem (X : Set ℚ) : Prop :=
  (∃ L : List (ℚ × ℚ), X = presentedIntervals L) ∧ X.Nonempty ∧ X ⊆ Set.Ico (0 : ℚ) 1

/-- Scott's master neighbourhood `Δ = [0,1)` for `𝒰`. -/
abbrev UMaster : Set ℚ := Set.Ico (0 : ℚ) 1

/-- `[0,1)` is presented by the single interval `[0,1)`. -/
theorem U_master_mem : UMem UMaster :=
  ⟨⟨[(0, 1)], by rw [presentedIntervals_cons, presentedIntervals_nil, Set.union_empty]⟩,
    ⟨0, by norm_num⟩, subset_rfl⟩

/-- Scott's token set `[0,1)` is non-empty. -/
theorem UMaster_nonempty : UMaster.Nonempty := by
  exact ⟨0, by simp [UMaster]⟩

/-- Intersection of two presentable sets is presentable, via `combineIntervals`. -/
theorem U_inter_mem {X Y Z : Set ℚ} (hX : UMem X) (hY : UMem Y) (hZ : UMem Z)
    (hZsub : Z ⊆ X ∩ Y) : UMem (X ∩ Y) := by
  rcases hX with ⟨⟨L1, rfl⟩, -, hXsub⟩
  rcases hY with ⟨⟨L2, rfl⟩, -, -⟩
  rcases hZ with ⟨-, hZne, -⟩
  exact ⟨⟨combineIntervals L1 L2, presentedIntervals_inter L1 L2⟩,
    hZne.mono hZsub, Set.inter_subset_left.trans hXsub⟩

/-- Every `UMem` set is contained in `[0,1)`. -/
theorem U_sub_master {X : Set ℚ} (hX : UMem X) : X ⊆ UMaster := hX.2.2

/-- **Definition 8.7 (Scott 1981, PRG-19).** The neighbourhood system `𝒰` over `[0,1) ⊆ ℚ`: its
neighbourhoods are the non-empty subsets of `[0,1)` presentable as a finite union of rational
intervals `[r,s)` (see the module docstring for why the raw endpoints need no `0 ≤ r < s ≤ 1`
side-condition, and `mem_iff_scott` for the literal reconciliation). Proof fields are named
theorems so Palomar can lock this value without generated `._proof_N` constants. -/
def U : NeighborhoodSystem ℚ where
  mem := UMem
  master := UMaster
  master_nonempty := UMaster_nonempty
  master_mem := U_master_mem
  inter_mem := U_inter_mem
  sub_master := U_sub_master

/-! ### Faithfulness: `U.mem` literally matches Scott's per-pair-bounded description -/

/-- Clip an interval-pair to `[0,1)`, moving `r` up to `0` and `s` down to `1` when needed. -/
private def clip (p : ℚ × ℚ) : ℚ × ℚ := (p.1 ⊔ 0, p.2 ⊓ 1)

private theorem presentedIntervals_map_clip (L : List (ℚ × ℚ)) :
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

private def clipLt (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1, p.2 ⊓ m)
private def clipGe (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1 ⊔ m, p.2)

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
end DomainTheory.Neighborhood
