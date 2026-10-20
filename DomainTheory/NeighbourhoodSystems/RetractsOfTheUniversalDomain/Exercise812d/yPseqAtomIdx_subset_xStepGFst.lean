module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG_fst_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_invariant
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.ySubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairIdx0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairIdx1
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.ySubStep_junk_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.junk_eq_zero_of_selectFn_eq_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep_correct
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.ySubStep_correct
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState_correct
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk_eq_zero_of_yPseqAtomJunk

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section YPseqCodeIFormula

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hxSplit : SplitSpec' D₁ splitX)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hySplit : SplitSpec' D₀ splitY)
  (hD₀mne : D₀.master.Nonempty) (hD₁mne : D₁.master.Nonempty)
  (hUnion0 : IsComputableUnion P₀)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 800000 in

/-- **The `Y`-side atom's `D₀`-index, subset of the depth-`n`-plus-half-step `X`-sub-step output.**
The `Y`-side twin of `(b)(i)`'s `xPseqAtomIdx_subset_atomPairIdx1`, but one half-step deeper:
`yPseqAtomIdx`'s genuine value is always `⊆` the `xStepG`-level set the inner (free-`bx`) `X`-sub-step
produces at depth `n`, via `hySplit`'s unconditional `∪ = A1`-field applied to that inner
`xSubStep_correct`/`ySubStep_correct` identification. -/
theorem yPseqAtomIdx_subset_xStepGFst {n i : ℕ} (b : Bool)
    (hjunk : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0) = 0) :
    P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i (if b then 1 else 0)) ⊆
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1 := by
  set s0 := packState2
      (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) with hs0def
  set s1 := xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair (if b then 1 else 0) s0))
    with hs1def
  have h : stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair 1 s1))) = 0 := by
    have h' := hjunk
    unfold yPseqAtomJunk yPseqAtomState at h'
    rwa [← hs0def, ← hs1def] at h'
  have hxnonjunk : stateJunk s1 = 0 := by
    have h2 := h
    rw [ySubStep_junk_eq, selectFn_one] at h2
    exact junk_eq_zero_of_selectFn_eq_zero h2
  have hAjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 :=
    atomPairJunk_eq_zero_of_yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY b hjunk
  obtain ⟨hidx0, hidx1⟩ := atomPairCodeState_correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n
    hAjunk
  have hidx0' : P₀.X (stateIdx0 s0) =
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 := by
    rw [hs0def, stateIdx0_packState2]; exact hidx0
  have hidx1' : P₁.X (stateIdx1 s0) =
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 := by
    rw [hs0def, stateIdx1_packState2]; exact hidx1
  obtain ⟨ihAB, -, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
  obtain ⟨hxc0, hxc1⟩ := xSubStep_correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin
    hxSplit hidx0' hidx1' ihAB ihB b hxnonjunk
  rw [← hs1def] at hxc0 hxc1
  have hAmem : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1 = ∅ ∨
      D₀.mem (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1 :=
    Or.inr (hxc0 ▸ P₀.mem_X _)
  have hBA : (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).2 = ∅ ↔
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1 = ∅ := by
    have hspec1 := hxSplit ihAB ihB (P₀.X n)
    by_cases hb : b = true
    · simp only [xStepG, xyStep, hb, ite_true]; exact hspec1.2.2.1.symm
    · simp only [xStepG, xyStep, hb]; exact hspec1.2.2.2.1.symm
  obtain ⟨hyc0, -⟩ := ySubStep_correct P₀ P₁ hDiff1 splitY hSplitY hD₁pos hD₁diff hD₁nomin hySplit
    hxc0 hxc1 hBA hAmem true h
  have hgoaleq : P₀.X (yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0)) =
      (yStepG splitY (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n) b).2
        (P₁.X n) true).1 := by
    show P₀.X (stateIdx0 (yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0))) = _
    unfold yPseqAtomState
    rw [← hs0def, ← hs1def]
    exact hyc0
  rw [hgoaleq]
  exact yStepG_fst_subset hySplit hBA hAmem (P₁.X n) true

end YPseqCodeIFormula

end DomainTheory.NeighbourhoodSystems
