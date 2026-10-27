module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPairCodeState

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

noncomputable def atomPairJunk (n k : ℕ) : ℕ :=
  stateJunk (stateInnerC (atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    (Nat.pair k n)))

end AtomPairCode

namespace atomPairJunk
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem zero (k : ℕ) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 k = 0 := by
  unfold atomPairJunk
  simp [atomPairCodeState, atomPairBase, stateBase2]

theorem eq_zero_of_succ {k n : ℕ}
    (h : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (n + 1) k = 0) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0 := by
  unfold atomPairJunk at h ⊢
  rw [atomPairCodeState.succ] at h
  unfold atomPairStep pcN pcT xwB1 xwS at h
  simp only [unpair_pair_fst, unpair_pair_snd, stateInnerC_packStateC] at h
  rw [ySubStep.junk_eq] at h
  have h1 := junk_eq_zero_of_selectFn_eq_zero h
  rw [xSubStep.junk_eq] at h1
  exact junk_eq_zero_of_selectFn_eq_zero h1

theorem le_one (k n : ℕ) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k ≤ 1 := by
  induction n with
  | zero => simp [atomPairJunk, atomPairCodeState, atomPairBase, stateBase2]
  | succ n ih =>
    unfold atomPairJunk at ih ⊢
    rw [atomPairCodeState.succ]
    unfold atomPairStep pcN pcT xwB1 xwS
    simp only [unpair_pair_fst, unpair_pair_snd, stateInnerC_packStateC]
    set T := atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (Nat.pair k n)
    rw [ySubStep.junk_eq, xSubStep.junk_eq]
    have hb1 : stateRemC T % 2 ≤ 1 := Nat.le_of_lt_succ (by omega)
    have hb2 : stateRemC T / 2 % 2 ≤ 1 := Nat.le_of_lt_succ (by omega)
    exact selectFn.le_one
      (selectFn.le_one ih (le_refl 1)
        (selectFn.le_one hb1 (emptyInterDec.le_one P₀ _) (IsComputableDiff.emptyDiffDec.le_one P₀ hDiff0 _)))
      (le_refl 1)
      (selectFn.le_one hb2 (emptyInterDec.le_one P₁ _) (IsComputableDiff.emptyDiffDec.le_one P₁ hDiff1 _))

end atomPairJunk


section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

noncomputable def atomPairIdx0 (n k : ℕ) : ℕ :=
  stateIdx0 (stateInnerC (atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    (Nat.pair k n)))

noncomputable def atomPairIdx1 (n k : ℕ) : ℕ :=
  stateIdx1 (stateInnerC (atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    (Nat.pair k n)))

end AtomPairCode

end DomainTheory.NeighbourhoodSystems
