/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.NoMinimal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.DiffClosed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.SplitSpec'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.splitChoice'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xyStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.extendTruePair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.restrictFinPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.yStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedδ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.deinterleaveδ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.toD1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.toD0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.domainIso812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.exists_split'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.splitChoice'_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.if_swap_disjoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.inter_diff_self_eq_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.inter_diff_eq_diff_of_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.genAtom_succ'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xyStep_disjoint_of_ne
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.extendTruePair_restrictFinPair_agree
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_fst_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_snd_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.yStep_fst_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.yStep_snd_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_disjoint_of_ne
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.yStep_disjoint_of_ne
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.inter_mem_or_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.diff_mem_or_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_eq_master_diff_inter_compl
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.iUnion_mem_or_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_succ_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_invariant
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_fst_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_snd_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_fst_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_snd_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_disjoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.subset_XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_snd_eq_inter_XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_snd_succ_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.subset_YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.xStep_spec_bit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.yStep_fst_eq_inter_YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.yStep_fst_succ_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq_empty_or_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_empty_or_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedX_even
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedX_odd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY_even
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY_odd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedδ_even
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedδ_odd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.genAtom_combinedX_succ_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.genAtom_combinedY_succ_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_fst_eq_genAtom
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.atomPair_snd_eq_genAtom
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedδ_deinterleaveδ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.hcore_even
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.hcore_odd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.hcore
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedX_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.combinedY_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.transfer_empty_combined
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.transfer_subset_combined
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.transfer_inter_empty_combined
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.transfer_double_subset_combined
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.transfer_inter_eq_combined
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.X_subset_iff_XPseq_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.X_inter_empty_iff_XPseq_inter_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_inter_empty_iff_Y_inter_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.X_inter_eq_iff_XPseq_inter_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_inter_eq_iff_Y_inter_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.X_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.Y_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.X_eq_empty_iff_XPseq_eq_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.Y_eq_empty_iff_YPseq_eq_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.X_subset_YPseq_iff_XPseq_subset_Y
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.YPseq_subset_X_iff_Y_subset_XPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.exists_inter_index_X
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.exists_inter_index_Y
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.XPseq_eq_Y_iff_X_eq_YPseq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.X_eq_iff_XPseq_eq

@[expose] public section

/-!
# Exercise 8.12(c) (Scott 1981, PRG-19, Lecture VIII) — a general two-sided back-and-forth lemma

Following the 7-part plan recorded in `arxiv.md`/`HANDOFF.md`, this file works towards **Exercise
8.12(c)**: a new, general (non-effective) lemma that two countable, atomless neighbourhood systems,
each satisfying a mutual one-step extension property relative to the other, are order-isomorphic.

## A structural shortcut over `Theorem88.lean`'s one-sided embedding

`Theorem88.lean`'s back-and-forth (`exists_split`/`atomU`/`Yseq`) embeds an *arbitrary* countable
`D` into `U` by tracking a matching pair `(A, B)` where only the `U`-side `B` is kept a genuine
`U`-neighbourhood-or-∅ at every step (via `U_no_minimal`); the `D`-side atom `A` is *never* required
to be a `D`-neighbourhood — it is an uninterpreted Boolean combination of `D`'s own sets and their
*complements* (`Δ \ Xᵢ`), which need not lie in `D` at all. This asymmetry is exactly what makes a
one-sided *embedding* enough, but is also exactly what breaks for a genuine two-sided
*isomorphism*: to alternately refine **both** sides (sometimes splitting `D₀`'s atom via `D₀`'s own
no-minimal property, sometimes `D₁`'s), the side not currently being split still needs to remain a
genuine neighbourhood-or-∅ at every step, including right after being intersected/subtracted by an
enumerated neighbourhood from the *other* side.

**Key discovery**: both `U` and `V` are already *Boolean-closed* — closed not just under
consistent intersection (Definition 1.1(ii)) but under **set-difference** of any two of their own
neighbourhoods (`U_diff_mem`, `V_diff_mem` below), on top of their already-known closure under
finite union (`U_union_mem`/`V_union_mem`) and unconditional/positive intersection
(`U`'s `combineIntervals`, `V`'s `levelSet_inter`, both witness-free). `U`'s case is nearly free:
`IntervalPrimrec.lean`'s `diffLists`/`presentedIntervals_diffLists` (built for the *computable*
presentation, Exercise 7.22-style) already witnesses this unconditionally, so `U_diff_mem` is a
two-line corollary. `V`'s case is the bitmask arithmetic identity `a ^^^ (a &&& b)` = "`a` and not
`b`", mirroring `levelSet_inter`'s own `upsample`-then-`&&&` formula.

Boolean-closure means a **complement-relative-to-master is always mem-or-∅** (`X \ D.master`, or
rather `D.master \ X`, is a special case with `Y := D.master`), and hence *every finite Boolean
combination* of enumerated neighbourhoods and their complements (`genAtom`, `Theorem88.lean`'s own
notion) is *automatically* mem-or-∅ by a direct induction — no `Classical.choice`-driven splitting
needed to keep either side "in the family". This is the structural fact that will let the two-sided
construction alternate which side is intersected/subtracted (a free computation) against which side
is split via the *other* system's no-minimal property (the one place non-constructive choice
genuinely enters, exactly as in `Theorem88.lean`), symmetrically.

## Status

This file establishes:

1. The Boolean-closure prerequisites `U_diff_mem`/`V_diff_mem` (and `U_isPositive`/`V_isPositive`,
 `U_noMinimal`/`V_noMinimal` repackaging the existing `U_no_minimal`/`V_no_minimal`).
2. The generic definitions (`NeighborhoodSystem.NoMinimal`, `.DiffClosed`) the back-and-forth is
 stated over, plus `genAtom_mem_or_empty` (Boolean atoms are automatically mem-or-∅ — no choice
 needed) and its one-step building blocks `inter_mem_or_empty`/`diff_mem_or_empty`.
3. `exists_split'`/`SplitSpec'`/`splitChoice'`: `Theorem88.lean`'s `exists_split`/`SplitSpec`/
 `splitChoice`, generalized from the hardcoded target `U` to an abstract atomless `E`.
4. **`atomPair`/`atomPair_invariant`**: the interleaved two-sided atom construction and its core
 invariant (matched emptiness, mem-or-∅ on both sides at every depth). This is the technical heart
 of the two-sided back-and-forth — see the section docstring above `atomPair` for the construction.

**Not yet done** (tracked as 8.12(c)'s remaining work): pairwise disjointness of `atomPair` across
disagreeing sign sequences (needed for a `Yseq`-style closed form on *both* sides at once), the
resulting `Xseq`/`Yseq`-analogue transfer lemmas (subset/inter-empty/inter-eq, mirroring
`Theorem88.lean`'s `transfer_subset_iff`/`transfer_inter_eq_iff` but bidirectionally), and the final
assembly into `DomainIso D₀ D₁`. This remaining work is comparable in size to the rest of
`Theorem88.lean` (`Yseq` onward) plus `Theorem88a.lean`'s assembly, done twice (once per direction)
plus the interleaving glue — a substantial next increment, tracked in `HANDOFF.md`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-! ### `U` is difference-closed -/

/-! ### `V` is difference-closed -/

/-! ### Generic hypotheses for the back-and-forth lemma -/




/-! ### `U` and `V` are Positive (Exercise 1.19) -/

/-! ### Boolean atoms are automatically mem-or-empty

The key structural payoff of Positivity + difference-closure: `Theorem88.lean`'s `genAtom`
(a finite Boolean combination of an enumerated family `Z 0, …, Z (n-1)` and their complements
relative to `M`) is *automatically* `D.mem`-or-`∅`, by a direct induction — no
`Classical.choice`-driven splitting is needed to keep it "in the family". This is what will let the
eventual two-sided back-and-forth alternate which side is refined by plain intersection/difference
(free) against which side is refined by the *other* system's `NoMinimal` property (the one place
genuine choice enters, exactly as in `Theorem88.lean`). -/
theorem genAtom_mem_or_empty {γ : Type*} {D : NeighborhoodSystem γ} (hpos : D.IsPositive)
    (hdiff : D.DiffClosed) {Z : ℕ → Set γ} (hZ : ∀ n, D.mem (Z n)) (δ : ℕ → Bool) :
    ∀ n, genAtom Z D.master δ n = ∅ ∨ D.mem (genAtom Z D.master δ n) := by
  intro n
  induction n with
  | zero => exact Or.inr D.master_mem
  | succ n ih =>
    have hbranch : (if δ n then Z n else D.master \ Z n) = ∅ ∨
        D.mem (if δ n then Z n else D.master \ Z n) := by
      by_cases hδ : δ n = true
      · simp only [hδ, ite_true]; exact Or.inr (hZ n)
      · simp only [hδ]; exact hdiff D.master_mem (hZ n)
    show genAtom Z D.master δ n ∩ (if δ n then Z n else D.master \ Z n) = ∅ ∨
      D.mem (genAtom Z D.master δ n ∩ (if δ n then Z n else D.master \ Z n))
    rcases ih with ihA | ihA
    · exact Or.inl (by rw [ihA, Set.empty_inter])
    rcases hbranch with hb | hb
    · exact Or.inl (by rw [hb, Set.inter_empty])
    rcases Set.eq_empty_or_nonempty (genAtom Z D.master δ n ∩ (if δ n then Z n else D.master \ Z n))
      with he | hne
    · exact Or.inl he
    · exact Or.inr ((hpos ihA hb).mpr hne)

/-! ### Generalizing `Theorem88.lean`'s `exists_split`/`SplitSpec`/`splitChoice` to an abstract
atomless target `E`

`Theorem88.lean`'s versions are hardcoded to `E := U`. The proofs below are verbatim transcriptions
with `U`/`U.mem`/`U_no_minimal` replaced by an abstract `E`/`E.mem`/`hEnomin : E.NoMinimal`; nothing
else changes. This is the piece that lets the eventual two-sided construction invoke the *same*
splitting lemma with `E := D₁` (when refining `D₁`'s side against a `D₀`-side target) and `E := D₀`
(symmetrically), rather than only ever `E := U`. -/





/-- **Generalization of `Theorem88.lean`'s `split_fst_subset`**: a splitting operation's first
output is a subset of `B` (from `I ∪ J = B`). -/
theorem split_fst_subset' {α γ : Type*} {E : NeighborhoodSystem γ}
    {split : Set α → Set γ → Set α → Set γ × Set γ} (hsplit : SplitSpec' E split)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α) :
    (split A B Xn).1 ⊆ B :=
  Set.subset_union_left.trans_eq (hsplit hAB hBE Xn).2.2.2.2.1

/-- **Generalization of `Theorem88.lean`'s `split_snd_subset`**: a splitting operation's second
output is a subset of `B` (from `I ∪ J = B`). -/
theorem split_snd_subset' {α γ : Type*} {E : NeighborhoodSystem γ}
    {split : Set α → Set γ → Set α → Set γ × Set γ} (hsplit : SplitSpec' E split)
    {A : Set α} {B : Set γ} (hAB : A = ∅ ↔ B = ∅) (hBE : B = ∅ ∨ E.mem B) (Xn : Set α) :
    (split A B Xn).2 ⊆ B :=
  Set.subset_union_right.trans_eq (hsplit hAB hBE Xn).2.2.2.2.1

/-! ### A single generic sub-step, used for both the `X`-sub-step and the `Y`-sub-step

`xyStep split A B Xn b` packages "intersect/subtract `A` by `Xn` directly (per the sign `b`), and
correspondingly split `B` via `split`" as a single ordinary (non-recursive) function. `atomPair`'s
two sub-steps per depth (the `X`-sub-step, splitting `D₁`'s side while directly refining `D₀`'s;
the `Y`-sub-step, splitting `D₀`'s side while directly refining `D₁`'s) are both literally
instances of this one function (`xStep`/`yStep` below) — exposing this lets the disjointness proof
manipulate one sub-step algebraically, rather than re-deriving `atomPair`'s definitional unfolding
by hand each time. -/







/-! ### Padding/restricting `ℕ → Bool × Bool` sign sequences

The two-sided analogues of `Theorem88.lean`'s `extendTrue`/`restrictFin`, built by applying them
componentwise to each half of the pair. Needed for 8.12(c)(vi)(4)'s `XPseq`/`YPseq`. -/




/-! ### The two named sub-steps of `atomPair`, as instances of `xyStep`

These, and their basic subset/disjointness properties, are stated fully generically (independent
of any particular `D₀`/`D₁`/`X`/`Y`) and placed here, *before* `section AtomPair` below, so that
they do not pick up that section's `include`d hypotheses (`hD₀pos`, `hXmem`, etc.) as spurious
extra arguments — `xStep`/`yStep` only ever need a *single* system's data (`D₁`/`hD₁nomin` for
`xStep`, `D₀`/`hD₀nomin` for `yStep`), never the full two-sided context. -/









/-! ### One-step Boolean-closure helpers

The two facts that let a mem-or-∅ set stay mem-or-∅ after being intersected/subtracted by a
*genuine* neighbourhood — the local, one-step content of `genAtom_mem_or_empty`'s induction,
extracted for reuse in the two-sided construction (where the "tested" side alternates, so the same
one-step fact is needed twice, once per side, rather than as a single long induction). -/



/-! ### A generic union-closure fact for `IsPositive` + `DiffClosed` systems

Needed by 8.12(c)(vi)(3)'s `YseqE_empty_or_mem`: `Theorem88.lean`'s own `U_union_mem`/
`U_iUnion_mem` (`Definition87.lean`) are proved directly from `U`'s presented-interval structure
(list `++`), which an abstract `E` does not have access to. But `IsPositive` + `DiffClosed` +
`sub_master`, entirely on their own, already force closure under finite union via the De Morgan
identity `X ∪ Y = M \ ((M \ X) ∩ (M \ Y))` (valid whenever `X, Y ⊆ M`) — `M \ X`/`M \ Y` are
mem-or-∅ by `DiffClosed`, their intersection is mem-or-∅ by `IsPositive`, and one more `DiffClosed`
application finishes it. This is genuinely new generic content (`U`/`V`'s own union-closure lemmas
never needed to be derived this way), not a transcription of anything in `Theorem88.lean`. -/




/-! ### The interleaved two-sided atom construction

Fix `D₀ : NeighborhoodSystem α`, `D₁ : NeighborhoodSystem β`, each Positive, difference-closed and
atomless (`NoMinimal`), with enumerations `X : ℕ → Set α`, `Y : ℕ → Set β` covering `D₀.mem`/`D₁.mem`
respectively. `atomPair` tracks a matched pair `(A, B) : Set α × Set β`, refined by *two* sub-steps
per index `n`: an **`X`-step** (test `A` against `X n` directly — free by Boolean-closure — and
correspondingly split `B` via `D₁`'s `NoMinimal`, exactly `Theorem88.lean`'s `exists_split` with
`E := D₁`), followed by a **`Y`-step** (symmetrically: test the *new* `B` against `Y n` directly,
and split the *new* `A` via `D₀`'s `NoMinimal`, `E := D₀`). A sign sequence `δ : ℕ → Bool × Bool`
selects the `+`/`-` branch at each of the two sub-steps. -/

section AtomPair

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))



variable (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin hXmem hYmem hD₀mne hD₁mne


/-! ### Pairwise disjointness of `atomPair` (Exercise 8.12(c)(v))

Mirrors `Theorem88.lean`'s `atomU_invariant`'s third clause, but proved on **both** sides at once.
Two supporting facts are needed first: `atomPair_congr` (agreeing sign sequences below `n` give the
identical depth-`n` pair — no invariant needed, purely definitional) and `atomPair_fst_subset`/
`atomPair_snd_subset` (each side only shrinks from depth `n` to `n+1` — *does* need the invariant,
since the shrinking is via `split_fst_subset'`/`split_snd_subset'`, which only fire once the
`SplitSpec'` preconditions are known to hold). -/








/-! ### Exercise 8.12(c)(vi)(4): recovering `X n` on `D₁`'s side directly from `atomPair`

**Correcting the original pre-plan.** The plan (`arxiv.md`/`HANDOFF.md`, written before any code)
anticipated a *bridge* identifying `atomPair`'s per-side trajectory with an instance of
`Exercise812cYseq.lean`'s single-family `atomE` (`E := D₁` for the `X`-sub-step, `E := D₀` for the
`Y`-sub-step). **This turns out to be false**, not just difficult: `atomE`'s testing family
`genAtom X Δ δ n` is a *free* Boolean combination (only ever intersected/subtracted directly,
never split), whereas `atomPair`'s `A`-component is *itself* choice-split at every `Y`-sub-step
(via `D₀.NoMinimal`) — so whenever `exists_split'`'s genuine-split case fires (generically), the
actual `A_n` is a *proper* subset of `genAtom X Δ δ₁ n` (`δ₁ k := (δ k).1`), with different
emptiness. Concretely: both `atomPair` components are "`atomE`-like" (choice-driven), so *neither*
is "`genAtom`-like" (free) — unlike `Theorem88.lean`'s one-sided case, where `D`'s side stayed free
by construction. `Exercise812cYseq.lean`'s apparatus therefore is **not** reused here (it remains
valid, reusable general theory for any genuinely one-sided abstract `E`, just not what this specific
bridge needs).

**The actual fix**, found by re-deriving `Yseq`'s "I-formula" argument directly against `atomPair`,
reusing only `atomPair_invariant`/`atomPair_congr`/`atomPair_disjoint` (already `Pass`, (iv)/(v))
and `xStep_snd_subset` (already `Pass`, (v)(2)) — no `atomE` involved: `XPseq n` unions, over all
depth-`n` histories, the `D₁`-piece obtained by the `X`-sub-step's "+" branch (the *half-step*
value, strictly before the following `Y`-sub-step further refines it). This is *simpler* than
`Yseq`'s own proof in one respect: since the branch is a literal argument (`true`) rather than
`δ n`'s own value, there is no need for `Theorem88.lean`'s `Function.update`-based "`δ2`" detour —
agreement below `n` alone suffices. -/





/-! ### Exercise 8.12(c)(vi)(4)(b)–(d): recovering `Y n` on `D₀`'s side directly from `atomPair`

Symmetric to `XPseq` above, but genuinely harder: `yStep`'s own inputs (the *post*-`X`-sub-step
values `A1`/`B1`) already depend on `(δ n).1` itself, not just history strictly below `n` — unlike
`xStep`'s inputs (`atomPair δ n`), which depend only on history strictly below `n`. So `YPseq`'s
union needs an *extra* free `Bool` parameter `bx` for position `n`'s `X`-sub-step bit ((b) below),
and relating an arbitrary such `bx` back to a concrete history's own bit needs a
`Function.update`-style bridge ((c) below, `xStep_spec_bit`, a drop-in generalization of
`xStep_spec` to an arbitrary bit rather than `δ n`'s own) before the "I-formula" itself ((d)) can
go through. -/






/-! ### Exercise 8.12(c)(vi)(5): `XPseq`/`YPseq` are always `D₁`/`D₀`-mem-or-∅

**First, achievable piece.** The full pre-planned content of (vi)(5)/(vi)(6) — an order/intersection
"transfer" layer recovering facts like `X i ⊆ X j ↔ XPseq i ⊆ XPseq j` (mirroring `Theorem88a.lean`'s
`embed_subset_iff`, needed for the eventual `DomainIso` assembly) — turns out to need a genuinely
new **joint two-family** atom/`genAtom`-style apparatus (testing points against *several* `X`
indices at once), not just the single-index `XPseq`/`YPseq` built in (vi)(4): unlike
`Theorem88a.lean`'s `idxSet` (always non-empty by pure index bookkeeping, independent of `D`'s own
`mem` structure), `atomPair`'s atoms can genuinely vanish, so relating *two* indices' inclusion
needs evaluating a *joint* atom, exactly why `Theorem88.lean`'s own `genAtom`/`transfer_empty_iff`
apparatus takes finite *lists* of constraints rather than single indices. That joint apparatus is
real, substantial new work, not yet scoped — deferred to a later sub-step once (vi)(5)/(vi)(6) chart
its precise shape. **What *is* immediately available**, reusing (vi)(3)'s fully generic
`iUnion_mem_or_empty` (no new theory needed): `XPseq n`/`YPseq n` are themselves always `D₁`/`D₀`
mem-or-∅, since each is a `Fintype`-indexed union of mem-or-∅ pieces (`SplitSpec'`'s own guarantee
on each `xStep`/`yStep` output). -/





/-! ### Exercise 8.12(c)(vi)(5)(b): `atomPair` as a `genAtom` over an interleaved family

The interleaved families `combinedX`/`combinedY` and shared sign-interleaving map `combinedδ`
(mirroring `Theorem88.lean`'s `atomU_eq_genAtom`, but half-stepped): `combinedX` alternates between
`X`'s own enumeration (even positions) and `YPseq`'s recovered `D₀`-side pieces (odd positions);
`combinedY` alternates symmetrically between `XPseq` (even) and `Y` (odd); `combinedδ` interleaves
`δ`'s two components the same way. The headline facts, `atomPair_fst_eq_genAtom`/
`atomPair_snd_eq_genAtom` below, identify `atomPair δ n`'s two sides with `genAtom` over these
families at depth `2 * n` — proved via the odd-depth half-step identities `genAtom_combinedX_succ_eq`/
`genAtom_combinedY_succ_eq`, which in turn are exactly (vi)(5)(a)'s two closed-form lemmas
(`yStep_fst_succ_eq`/`xStep_snd_succ_eq`) each performed once per level of `n`, as anticipated. -/














/-! ### Exercise 8.12(c)(vi)(5)(c)(1): de-interleaving a sign sequence, and its round trip

The first of the four sub-parts of (c)'s planned `hcore` fact for `transfer_dir`. Given an
arbitrary `δ' : ℕ → Bool` (a sign sequence for the *interleaved* families `combinedX`/`combinedY`),
`deinterleaveδ δ'` reads it two values at a time into a `ℕ → Bool × Bool` sign sequence for the
*paired* family `atomPair` — the inverse of `combinedδ`. `combinedδ_deinterleaveδ` confirms
re-interleaving recovers `δ'` exactly, feeding both (c)(2)'s even-index case and (c)(3)'s
odd-index case. -/






/-! ### Exercise 8.12(c)(vi)(5)(d): the headline bidirectional transfer facts

Instantiates `Theorem88.lean`'s fully generic `transfer_dir` with `Z1 := combinedX`,
`M1 := D₀.master`, `Z2 := combinedY`, `M2 := D₁.master`, and (c)'s `hcore`, transcribing
`Theorem88.lean`'s own `transfer_empty_iff`/`transfer_subset_iff`/`transfer_inter_empty_iff`/
`transfer_double_subset_iff`/`transfer_inter_eq_iff` (all hardcoded to the concrete `X`/`Δ`/
`Yseq split X Δ`/`U.master`, hence not directly reusable) one-for-one with `Δ ↦ D₀.master`,
`X ↦ combinedX`, `U.master ↦ D₁.master`, `Yseq split X Δ ↦ combinedY`. The headline deliverable
(further down) then specializes each even/even and odd/odd index pair back down to plain
statements about `X`/`XPseq` and `YPseq`/`Y`, unfolding via (b)'s `combinedX_even`/`combinedX_odd`/
`combinedY_even`/`combinedY_odd` and discharging the `∩ master` bookkeeping with `D₀.sub_master`/
`XPseq_subset_master`/`YPseq_subset_master`/`D₁.sub_master`. -/








/-! ### The headline facts: specializing `transfer_*_combined` to even/even and odd/odd indices

The actual deliverable of Exercise 8.12(c)(vi)(5): plain statements about `X`/`XPseq` (from the
even-index specialization) and `YPseq`/`Y` (from the odd-index specialization), needed for (vii)'s
`DomainIso` assembly. -/


theorem YPseq_subset_iff_Y_subset (i j : ℕ) :
    YPseq D₀ D₁ hD₀nomin hD₁nomin X Y i ⊆ YPseq D₀ D₁ hD₀nomin hD₁nomin X Y j ↔ Y i ⊆ Y j := by
  have key := transfer_subset_combined D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y
    hXmem hYmem hD₀mne hD₁mne (2 * i + 1) (2 * j + 1)
  rw [combinedX_odd, combinedX_odd, combinedY_odd, combinedY_odd,
    Set.inter_eq_self_of_subset_right
      (YPseq_subset_master D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem
        hD₀mne hD₁mne i),
    Set.inter_eq_self_of_subset_right (D₁.sub_master (hYmem i))] at key
  exact key





/-! ### Exercise 8.12(c)(vi)(7): the bidirectional "genuine neighbourhood" glue

The last ingredient (vii)'s `DomainIso` assembly needs beyond (5)'s order/intersection transfer:
`X n`/`Y n` (being `hXmem`/`hYmem`'s enumerated sets) are *never* `∅` (`NoMinimal.mem_ne_empty`),
and — via the `i = j` case of (5)(d)'s inter-empty transfer, collapsed through `Set.inter_self` —
neither are their `atomPair`-images `XPseq`/`YPseq`. Combined with `XPseq_empty_or_mem`/
`YPseq_empty_or_mem` ((vi)(4)), this makes `XPseq n`/`YPseq n` *always genuine* neighbourhoods
(`D₁`'s/`D₀`'s resp.), completing the correspondence: no separate "mutual extension" hypothesis
beyond `NoMinimal` on both sides is needed. -/









end AtomPair

/-! ### Exercise 8.12(c)(vii): assembling `DomainIso D₀ D₁`

Adds the hypotheses `section AtomPair`'s own docstring already assumed but never formally
declared: `X`/`Y` **cover** `D₀.mem`/`D₁.mem` (`hXcover`/`hYcover`, mirroring `Theorem88a.lean`'s
`hcover`), and Scott's zero-convention `X 0 = D₀.master`/`Y 0 = D₁.master` (mirroring `he0`). -/

section Iso

variable {α β : Type*} (D₀ : NeighborhoodSystem α) (D₁ : NeighborhoodSystem β)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (X : ℕ → Set α) (Y : ℕ → Set β) (hXmem : ∀ n, D₀.mem (X n)) (hYmem : ∀ n, D₁.mem (Y n))
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hXcover : ∀ S, D₀.mem S ↔ ∃ n, S = X n) (hYcover : ∀ S, D₁.mem S ↔ ∃ n, S = Y n)
  (hX0 : X 0 = D₀.master) (hY0 : Y 0 = D₁.master)












include hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne hD₁mne hXcover
  hYcover hX0 hY0 in
/-- **Exercise 8.12(c)(vii)(6), headline.** `D₀ ≅ᴰ D₁`: completes Exercise 8.12(c) in full. -/
theorem isomorphic_812c : D₀ ≅ᴰ D₁ :=
  ⟨domainIso812c D₀ D₁ hD₀pos hD₀diff hD₀nomin hD₁pos hD₁diff hD₁nomin X Y hXmem hYmem hD₀mne
    hD₁mne hXcover hYcover hX0 hY0⟩
end Iso
end DomainTheory.NeighbourhoodSystems
