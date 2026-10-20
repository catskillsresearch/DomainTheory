/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_invariant
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyDiffDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyDiffDec_le_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyDiffDec_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairIdx0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairIdx1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep_junk_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.ySubStep_junk_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep_correct
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState_correct
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomJunk

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section YPseqCodeUnconditional

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty) (hUnion0 : IsComputableUnion P₀)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
/-- **The half-step-`bx` atom is non-junk, given the classical split piece meets `P₁.X n`.** The
one-bit-generic engine behind `yPseqAtomJunk_exists_zero`: given the incoming depth-`n` state is
non-junk (`hjunk0`) and, for a *chosen* bit `b`, both the direct-refine piece `A1(b) ≠ ∅` (`hne`)
and the split piece meets `P₁.X n` non-trivially (`hinter`), the half-step atom
`yPseqAtomJunk n i (if b then 1 else 0)` is `0`. Chases `xSubStep`'s own junk formula down to
`emptyInterDec`/`emptyDiffDec` (`P₀`-side, from `hne` via `atomPairCodeState_correct`'s forward
identification) to get `xSubStep`'s output non-junk, then `xSubStep_correct` to identify its
`D₁`-side index with the classical split piece, then the same `emptyInterDec` reading (`P₁`-side,
from `hinter`) collapses `ySubStep`'s own forced-`"+"` junk check to `0`. -/
theorem yPseqAtomJunk_eq_zero_of_bit {i n : ℕ}
    (hjunk0 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0) (b : Bool)
    (hne : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1 ≠ ∅)
    (hinter : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).2 ∩ P₁.X n ≠ ∅) :
    yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i (if b then 1 else 0) = 0 := by
  obtain ⟨hidx0, hidx1⟩ := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n
    hjunk0
  have hxc0 : selectFn (if b then 1 else 0)
      (emptyInterDec P₀ (Nat.pair (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        n i) n))
      (emptyDiffDec P₀ hDiff0 (Nat.pair (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY n i) n)) = 0 := by
    by_cases hb : b = true
    · simp only [xStepG, xyStep, hb, ite_true] at hne
      have hne' : P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) ∩
          P₀.X n ≠ ∅ := by rw [hidx0]; exact hne
      simp only [hb, ite_true, selectFn_one]
      by_contra hcon
      have hle := emptyInterDec_le_one P₀ (Nat.pair
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n)
      have h1 : emptyInterDec P₀ (Nat.pair
          (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n) = 1 := by omega
      exact hne' ((emptyInterDec_eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h1)
    · simp only [xStepG, xyStep, hb, Bool.false_eq_true, ite_false] at hne
      have hne' : P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) \
          P₀.X n ≠ ∅ := by rw [hidx0]; exact hne
      simp only [hb, Bool.false_eq_true, ite_false, selectFn_zero]
      by_contra hcon
      have hle := emptyDiffDec_le_one P₀ hDiff0 (Nat.pair
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n)
      have h1 : emptyDiffDec P₀ hDiff0 (Nat.pair
          (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n) = 1 := by omega
      exact hne' ((emptyDiffDec_eq_one_iff P₀ hDiff0 hD₀diff hD₀nomin _ _).mp h1)
  set s0 := packState2
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) with hs0def
  have hidx0' : P₀.X (stateIdx0 s0) =
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 := by
    rw [hs0def, stateIdx0_packState2]; exact hidx0
  have hidx1' : P₁.X (stateIdx1 s0) =
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 := by
    rw [hs0def, stateIdx1_packState2]; exact hidx1
  set s1 := xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair (if b then 1 else 0) s0))
    with hs1def
  have hxnonjunk : stateJunk s1 = 0 := by
    rw [hs1def, xSubStep_junk_eq, hs0def, stateJunk_packState2, stateIdx0_packState2, hjunk0,
      selectFn_zero]
    exact hxc0
  obtain ⟨hAB, -, hBmem⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
  obtain ⟨-, hxB1⟩ := xSubStep_correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin hxSplit
    hidx0' hidx1' hAB hBmem b hxnonjunk
  rw [← hs1def] at hxB1
  have hB1inter : P₁.X (stateIdx1 s1) ∩ P₁.X n ≠ ∅ := by rw [hxB1]; exact hinter
  have hyc0 : emptyInterDec P₁ (Nat.pair (stateIdx1 s1) n) = 0 := by
    by_contra hcon
    have hle := emptyInterDec_le_one P₁ (Nat.pair (stateIdx1 s1) n)
    have h1 : emptyInterDec P₁ (Nat.pair (stateIdx1 s1) n) = 1 := by omega
    exact hB1inter ((emptyInterDec_eq_one_iff P₁ hD₁pos hD₁nomin _ _).mp h1)
  unfold yPseqAtomJunk yPseqAtomState
  rw [← hs0def, ← hs1def, ySubStep_junk_eq, selectFn_one, hxnonjunk, selectFn_zero]
  exact hyc0

end YPseqCodeUnconditional

end DomainTheory.NeighbourhoodSystems
