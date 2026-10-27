module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.domainIso812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yStepG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

def packState2 (idx0 idx1 junk : ℕ) : ℕ := Nat.pair idx0 (Nat.pair idx1 junk)

def stateIdx0 (s : ℕ) : ℕ := s.unpair.1

@[simp] theorem stateIdx0_packState2 (a b c : ℕ) : stateIdx0 (packState2 a b c) = a := by
  unfold stateIdx0 packState2; simp only [unpair_pair_fst]

def stateIdx1 (s : ℕ) : ℕ := s.unpair.2.unpair.1

@[simp] theorem stateIdx1_packState2 (a b c : ℕ) : stateIdx1 (packState2 a b c) = b := by
  unfold stateIdx1 packState2; simp only [unpair_pair_fst, unpair_pair_snd]

def stateJunk (s : ℕ) : ℕ := s.unpair.2.unpair.2

@[simp] theorem stateJunk_packState2 (a b c : ℕ) : stateJunk (packState2 a b c) = c := by
  unfold stateJunk packState2; simp only [unpair_pair_snd]

def packStateC (rem s : ℕ) : ℕ := Nat.pair rem s

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

def xwB1 (w : ℕ) : ℕ := w.unpair.2.unpair.1

def xwN (w : ℕ) : ℕ := w.unpair.1

def xwS (w : ℕ) : ℕ := w.unpair.2.unpair.2

end XSubStep

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

def stateRemC (t : ℕ) : ℕ := t.unpair.1

namespace stateRemC
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

@[simp] theorem packStateC (a b : ℕ) : stateRemC (_root_.DomainTheory.NeighbourhoodSystems.packStateC a b) = a := by
  unfold stateRemC _root_.DomainTheory.NeighbourhoodSystems.packStateC; simp only [unpair_pair_fst]

end stateRemC
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

def stateBase2 (masterIdx0 masterIdx1 : ℕ) : ℕ := packState2 masterIdx0 masterIdx1 0

def stateInnerC (t : ℕ) : ℕ := t.unpair.2

@[simp] theorem stateInnerC_packStateC (a b : ℕ) : stateInnerC (packStateC a b) = b := by
  unfold stateInnerC packStateC; simp only [unpair_pair_snd]

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

def atomPairBase (k : ℕ) : ℕ := packStateC k (stateBase2 P₀.masterIdx P₁.masterIdx)

end AtomPairCode

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

noncomputable def xSubStep (w : ℕ) : ℕ :=
  let n := xwN w
  let b1 := xwB1 w
  let s := xwS w
  let idx0 := stateIdx0 s
  let idx1 := stateIdx1 s
  let junk := stateJunk s
  let directIdx := selectFn b1 (P₀.inter idx0 n) (hDiff0.diffIdx idx0 n)
  let directEmpty := selectFn b1 (emptyInterDec P₀ (Nat.pair idx0 n))
    (IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair idx0 n))
  let splitIdx := selectFn b1 (hSplitX.posIdx idx0 idx1 n) (hSplitX.negIdx idx0 idx1 n)
  let newJunk := selectFn junk 1 directEmpty
  packState2 (selectFn newJunk 0 directIdx) (selectFn newJunk 0 splitIdx) newJunk

end XSubStep


section YSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff1 : IsComputableDiff P₁)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

noncomputable def ySubStep (w : ℕ) : ℕ :=
  let n := xwN w
  let b2 := xwB1 w
  let s := xwS w
  let idx0 := stateIdx0 s
  let idx1 := stateIdx1 s
  let junk := stateJunk s
  let directIdx := selectFn b2 (P₁.inter idx1 n) (hDiff1.diffIdx idx1 n)
  let directEmpty := selectFn b2 (emptyInterDec P₁ (Nat.pair idx1 n))
    (IsComputableDiff.emptyDiffDec P₁ hDiff1 (Nat.pair idx1 n))
  let splitIdx := selectFn b2 (hSplitY.posIdx idx1 idx0 n) (hSplitY.negIdx idx1 idx0 n)
  let newJunk := selectFn junk 1 directEmpty
  packState2 (selectFn newJunk 0 splitIdx) (selectFn newJunk 0 directIdx) newJunk

end YSubStep

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

def pcN (w : ℕ) : ℕ := xwB1 w

def pcT (w : ℕ) : ℕ := xwS w

noncomputable def atomPairStep (w : ℕ) : ℕ :=
  let n := pcN w
  let T := pcT w
  let rem := stateRemC T
  let s := stateInnerC T
  let b1 := rem % 2
  let b2 := (rem / 2) % 2
  let s1 := xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair b1 s))
  let s2 := ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair b2 s1))
  packStateC (rem / 4) s2

noncomputable def atomPairCodeState (t : ℕ) : ℕ :=
  t.unpair.2.rec (atomPairBase P₀ P₁ t.unpair.1) (fun y IH =>
    atomPairStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      (Nat.pair t.unpair.1 (Nat.pair y IH)))

end AtomPairCode

namespace atomPairCodeState
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem succ (k n : ℕ) :
    atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (Nat.pair k (n + 1)) =
      atomPairStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        (Nat.pair k (Nat.pair n (atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
          hSplitY (Nat.pair k n)))) := by
  unfold atomPairCodeState
  simp only [unpair_pair_fst, unpair_pair_snd]

end atomPairCodeState


theorem junk_eq_zero_of_selectFn_eq_zero {junk X : ℕ} (h : selectFn junk 1 X = 0) : junk = 0 := by
  rcases Nat.eq_zero_or_pos junk with h0 | h0
  · exact h0
  · exfalso; unfold selectFn at h; have : 1 ≤ junk := h0; nlinarith

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

namespace selectFn
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem le_one {c a b : ℕ} (hc : c ≤ 1) (ha : a ≤ 1) (hb : b ≤ 1) :
    selectFn c a b ≤ 1 := by
  rcases (show c = 0 ∨ c = 1 from by omega) with h | h <;> rw [h]
  · rw [selectFn_zero]; exact hb
  · rw [selectFn_one]; exact ha

theorem one_eq_zero_iff {c X : ℕ} : selectFn c 1 X = 0 ↔ c = 0 ∧ X = 0 := by
  constructor
  · intro h
    have hc0 : c = 0 := junk_eq_zero_of_selectFn_eq_zero h
    subst hc0
    simpa [selectFn_zero] using h
  · rintro ⟨rfl, rfl⟩
    simp [selectFn_zero]

end selectFn

theorem diffIdx_eq_of_empty_zero {γ : Type*} {W : NeighborhoodSystem γ} {Q : ComputablePresentation W}
    (hDiff : IsComputableDiff Q) {idx0 n0 : ℕ} (h : IsComputableDiff.emptyDiffDec Q hDiff (Nat.pair idx0 n0) = 0) :
    Q.X (hDiff.diffIdx idx0 n0) = Q.X idx0 \ Q.X n0 := by
  apply hDiff.diffIdx_spec
  have hle := IsComputableDiff.existsDiffDec.le_one Q hDiff (Nat.pair idx0 n0)
  have h1 : IsComputableDiff.existsDiffDec Q hDiff (Nat.pair idx0 n0) = 1 := by unfold IsComputableDiff.emptyDiffDec at h; omega
  exact (IsComputableDiff.existsDiffDec.spec Q hDiff idx0 n0).mp h1

theorem interIdx_eq_of_empty_zero {γ : Type*} {W : NeighborhoodSystem γ} (Q : ComputablePresentation W)
    {idx0 n0 : ℕ} (h : emptyInterDec Q (Nat.pair idx0 n0) = 0) :
    Q.X (Q.inter idx0 n0) = Q.X idx0 ∩ Q.X n0 := by
  apply Q.inter_spec
  have hle := existsInterDec.le_one Q (Nat.pair idx0 n0)
  have h1 : existsInterDec Q (Nat.pair idx0 n0) = 1 := by unfold emptyInterDec at h; omega
  exact (existsInterDec.spec Q idx0 n0).mp h1

namespace xSubStep
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

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

theorem idx0_eq {s n b1 : ℕ}
    (h : selectFn (stateJunk s) 1 (selectFn b1 (emptyInterDec P₀ (Nat.pair (stateIdx0 s) n))
      (IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 s) n))) = 0) :
    stateIdx0 (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair b1 s))) =
      selectFn b1 (P₀.inter (stateIdx0 s) n) (hDiff0.diffIdx (stateIdx0 s) n) := by
  unfold xSubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateIdx0_packState2, h,
    selectFn_zero]

theorem idx1_eq {s n b1 : ℕ}
    (h : selectFn (stateJunk s) 1 (selectFn b1 (emptyInterDec P₀ (Nat.pair (stateIdx0 s) n))
      (IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 s) n))) = 0) :
    stateIdx1 (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair b1 s))) =
      selectFn b1 (hSplitX.posIdx (stateIdx0 s) (stateIdx1 s) n)
        (hSplitX.negIdx (stateIdx0 s) (stateIdx1 s) n) := by
  unfold xSubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateIdx1_packState2, h,
    selectFn_zero]

theorem junk_eq (s n b1 : ℕ) :
    stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair b1 s))) =
      selectFn (stateJunk s) 1 (selectFn b1 (emptyInterDec P₀ (Nat.pair (stateIdx0 s) n))
        (IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 s) n))) := by
  unfold xSubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateJunk_packState2]

include hD₀pos hD₀nomin hD₀diff hxSplit in

theorem correct {s n : ℕ} {A : Set α} {B : Set β}
    (hA : P₀.X (stateIdx0 s) = A) (hB : P₁.X (stateIdx1 s) = B)
    (hAB : A = ∅ ↔ B = ∅) (hBmem : B = ∅ ∨ D₁.mem B) (b : Bool)
    (hnonjunk : stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair n (Nat.pair (if b then 1 else 0) s))) = 0) :
    P₀.X (stateIdx0 (xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair n (Nat.pair (if b then 1 else 0) s)))) = (xStepG splitX A B (P₀.X n) b).1 ∧
    P₁.X (stateIdx1 (xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair n (Nat.pair (if b then 1 else 0) s)))) = (xStepG splitX A B (P₀.X n) b).2 := by
  have hspec1 := hxSplit hAB hBmem (P₀.X n)
  subst hA; subst hB
  by_cases hb : b = true
  · simp only [xStepG, xyStep, hb, ite_true] at hnonjunk ⊢
    rw [xSubStep.junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn.one_eq_zero_iff.mp hnonjunk
    rw [selectFn_one] at hemp
    have hemp' : P₀.X (stateIdx0 s) ∩ P₀.X n ≠ ∅ :=
      (emptyInterDec.eq_one_iff P₀ hD₀pos hD₀nomin (stateIdx0 s) n).not.mp (by omega)
    have hne : (splitX (P₀.X (stateIdx0 s)) (P₁.X (stateIdx1 s)) (P₀.X n)).1 ≠ ∅ :=
      hspec1.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [xSubStep.idx0_eq (h := hnonjunk), selectFn_one]
      exact interIdx_eq_of_empty_zero P₀ hemp
    · rw [xSubStep.idx1_eq (h := hnonjunk), selectFn_one]
      exact (hSplitX.posIdx_spec (stateIdx0 s) (stateIdx1 s) n hne).symm
  · simp only [xStepG, xyStep, hb, Bool.false_eq_true, ite_false] at hnonjunk ⊢
    rw [xSubStep.junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn.one_eq_zero_iff.mp hnonjunk
    rw [selectFn_zero] at hemp
    have hemp' : P₀.X (stateIdx0 s) \ P₀.X n ≠ ∅ :=
      (IsComputableDiff.emptyDiffDec.eq_one_iff P₀ hDiff0 hD₀diff hD₀nomin (stateIdx0 s) n).not.mp (by omega)
    have hne : (splitX (P₀.X (stateIdx0 s)) (P₁.X (stateIdx1 s)) (P₀.X n)).2 ≠ ∅ :=
      hspec1.2.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [xSubStep.idx0_eq (h := hnonjunk), selectFn_zero]
      exact diffIdx_eq_of_empty_zero hDiff0 hemp
    · rw [xSubStep.idx1_eq (h := hnonjunk), selectFn_zero]
      exact (hSplitX.negIdx_spec (stateIdx0 s) (stateIdx1 s) n hne).symm

end xSubStep

namespace ySubStep
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

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

theorem idx0_eq {s n b2 : ℕ}
    (h : selectFn (stateJunk s) 1 (selectFn b2 (emptyInterDec P₁ (Nat.pair (stateIdx1 s) n))
      (IsComputableDiff.emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 s) n))) = 0) :
    stateIdx0 (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair b2 s))) =
      selectFn b2 (hSplitY.posIdx (stateIdx1 s) (stateIdx0 s) n)
        (hSplitY.negIdx (stateIdx1 s) (stateIdx0 s) n) := by
  unfold ySubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateIdx0_packState2, h,
    selectFn_zero]

theorem idx1_eq {s n b2 : ℕ}
    (h : selectFn (stateJunk s) 1 (selectFn b2 (emptyInterDec P₁ (Nat.pair (stateIdx1 s) n))
      (IsComputableDiff.emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 s) n))) = 0) :
    stateIdx1 (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair b2 s))) =
      selectFn b2 (P₁.inter (stateIdx1 s) n) (hDiff1.diffIdx (stateIdx1 s) n) := by
  unfold ySubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateIdx1_packState2, h,
    selectFn_zero]

theorem junk_eq (s n b2 : ℕ) :
    stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY (Nat.pair n (Nat.pair b2 s))) =
      selectFn (stateJunk s) 1 (selectFn b2 (emptyInterDec P₁ (Nat.pair (stateIdx1 s) n))
        (IsComputableDiff.emptyDiffDec P₁ hDiff1 (Nat.pair (stateIdx1 s) n))) := by
  unfold ySubStep
  simp only [xwN, xwB1, xwS, unpair_pair_fst, unpair_pair_snd, stateJunk_packState2]

include hD₁pos hD₁nomin hD₁diff hySplit in

theorem correct {s n : ℕ} {A : Set α} {B : Set β}
    (hA : P₀.X (stateIdx0 s) = A) (hB : P₁.X (stateIdx1 s) = B)
    (hBA : B = ∅ ↔ A = ∅) (hAmem : A = ∅ ∨ D₀.mem A) (b : Bool)
    (hnonjunk : stateJunk (ySubStep P₀ P₁ hDiff1 splitY hSplitY
        (Nat.pair n (Nat.pair (if b then 1 else 0) s))) = 0) :
    P₀.X (stateIdx0 (ySubStep P₀ P₁ hDiff1 splitY hSplitY
        (Nat.pair n (Nat.pair (if b then 1 else 0) s)))) = (yStepG splitY A B (P₁.X n) b).1 ∧
    P₁.X (stateIdx1 (ySubStep P₀ P₁ hDiff1 splitY hSplitY
        (Nat.pair n (Nat.pair (if b then 1 else 0) s)))) = (yStepG splitY A B (P₁.X n) b).2 := by
  have hspec2 := hySplit hBA hAmem (P₁.X n)
  subst hA; subst hB
  by_cases hb : b = true
  · simp only [yStepG, xyStep, Prod.swap, hb, ite_true] at hnonjunk ⊢
    rw [ySubStep.junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn.one_eq_zero_iff.mp hnonjunk
    rw [selectFn_one] at hemp
    have hemp' : P₁.X (stateIdx1 s) ∩ P₁.X n ≠ ∅ :=
      (emptyInterDec.eq_one_iff P₁ hD₁pos hD₁nomin (stateIdx1 s) n).not.mp (by omega)
    have hne : (splitY (P₁.X (stateIdx1 s)) (P₀.X (stateIdx0 s)) (P₁.X n)).1 ≠ ∅ :=
      hspec2.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [ySubStep.idx0_eq (h := hnonjunk), selectFn_one]
      exact (hSplitY.posIdx_spec (stateIdx1 s) (stateIdx0 s) n hne).symm
    · rw [ySubStep.idx1_eq (h := hnonjunk), selectFn_one]
      exact interIdx_eq_of_empty_zero P₁ hemp
  · simp only [yStepG, xyStep, Prod.swap, hb, Bool.false_eq_true, ite_false] at hnonjunk ⊢
    rw [ySubStep.junk_eq] at hnonjunk
    obtain ⟨-, hemp⟩ := selectFn.one_eq_zero_iff.mp hnonjunk
    rw [selectFn_zero] at hemp
    have hemp' : P₁.X (stateIdx1 s) \ P₁.X n ≠ ∅ :=
      (IsComputableDiff.emptyDiffDec.eq_one_iff P₁ hDiff1 hD₁diff hD₁nomin (stateIdx1 s) n).not.mp (by omega)
    have hne : (splitY (P₁.X (stateIdx1 s)) (P₀.X (stateIdx0 s)) (P₁.X n)).2 ≠ ∅ :=
      hspec2.2.2.2.1.not.mp hemp'
    refine ⟨?_, ?_⟩
    · rw [ySubStep.idx0_eq (h := hnonjunk), selectFn_zero]
      exact (hSplitY.negIdx_spec (stateIdx1 s) (stateIdx0 s) n hne).symm
    · rw [ySubStep.idx1_eq (h := hnonjunk), selectFn_zero]
      exact diffIdx_eq_of_empty_zero hDiff1 hemp

end ySubStep

end DomainTheory.NeighbourhoodSystems
