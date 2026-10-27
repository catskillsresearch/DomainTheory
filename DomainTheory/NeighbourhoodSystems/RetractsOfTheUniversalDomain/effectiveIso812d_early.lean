module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.domainIso812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomE
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPairG_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPairCodeState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.XFold
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.YFoldInner
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.XPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.YPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ComputableBisection
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_26

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

namespace stateRemC
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem atomPairCodeState (k n : ℕ) :
    stateRemC (_root_.DomainTheory.NeighbourhoodSystems.atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      (Nat.pair k n)) = k / 4 ^ n := by
  induction n with
  | zero => simp [_root_.DomainTheory.NeighbourhoodSystems.atomPairCodeState, atomPairBase]
  | succ n ih =>
    rw [atomPairCodeState.succ]
    unfold atomPairStep pcN pcT xwB1 xwS
    simp only [unpair_pair_fst, unpair_pair_snd, stateRemC.packStateC, ih,
      Nat.div_div_eq_div_mul, ← pow_succ]

end stateRemC
namespace atomPairCodeState
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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in

theorem correct (k n : ℕ)
    (hjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0) :
    P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) =
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).1 ∧
      P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) =
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).2 := by
  induction n with
  | zero =>
    unfold atomPairIdx0 atomPairIdx1
    simp [atomPairCodeState, atomPairBase, stateBase2]
    exact ⟨P₀.masterIdx_spec, P₁.masterIdx_spec⟩
  | succ n ih =>
    have hjunk_n := atomPairJunk.eq_zero_of_succ (h := hjunk)
    obtain ⟨hidx0, hidx1⟩ := ih hjunk_n
    unfold atomPairJunk at hjunk
    unfold atomPairIdx0 at hidx0
    unfold atomPairIdx1 at hidx1
    unfold atomPairIdx0 atomPairIdx1
    rw [atomPairCodeState.succ] at hjunk ⊢
    unfold atomPairStep pcN pcT xwB1 xwS at hjunk ⊢
    simp only [unpair_pair_fst, unpair_pair_snd, stateInnerC_packStateC] at hjunk hidx0 hidx1 ⊢
    set T := atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (Nat.pair k n)
      with hTdef
    have hrem : stateRemC T = k / 4 ^ n := stateRemC.atomPairCodeState P₀ P₁ hDiff0 hDiff1
      splitX hSplitX splitY hSplitY k n
    have hb1 : stateRemC T % 2 = if (deltaPair k n).1 then 1 else 0 := by
      rw [hrem]
      rcases Nat.mod_two_eq_zero_or_one (k / 4 ^ n) with h0 | h1
      · have hδ : (deltaPair k n).1 = false := by unfold deltaPair; simp [h0]
        simp [hδ, h0]
      · have hδ : (deltaPair k n).1 = true := by unfold deltaPair; simp [h1]
        simp [hδ, h1]
    have hb2 : stateRemC T / 2 % 2 = if (deltaPair k n).2 then 1 else 0 := by
      rw [hrem]
      rcases Nat.mod_two_eq_zero_or_one (k / 4 ^ n / 2) with h0 | h1
      · have hδ : (deltaPair k n).2 = false := by unfold deltaPair; simp [h0]
        simp [hδ, h0]
      · have hδ : (deltaPair k n).2 = true := by unfold deltaPair; simp [h1]
        simp [hδ, h1]
    rw [hb1] at hjunk ⊢
    rw [hb2] at hjunk ⊢
    have hxjunk : stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair n (Nat.pair (if (deltaPair k n).1 then 1 else 0) (stateInnerC T)))) = 0 := by
      have hj2 := hjunk
      rw [ySubStep.junk_eq] at hj2
      exact junk_eq_zero_of_selectFn_eq_zero hj2
    obtain ⟨hAB, -, hBmem⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair k) n
    obtain ⟨hx0, hx1⟩ := xSubStep.correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin
      hxSplit hidx0 hidx1 hAB hBmem (deltaPair k n).1 hxjunk
    have hxspec := xStepG.spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit
      P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair k) n
    rw [atomPairG.succ_eq]
    exact ySubStep.correct P₀ P₁ hDiff1 splitY hSplitY hD₁pos hD₁diff hD₁nomin hySplit hx0 hx1
      hxspec.1 hxspec.2 (deltaPair k n).2 hjunk

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in

theorem disjoint {n k k' : ℕ}
    (hk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0)
    (hk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k' = 0)
    (hne : ∃ i < n, deltaPair k i ≠ deltaPair k' i) :
    P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) ∩
        P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k') = ∅ ∧
      P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) ∩
        P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k') = ∅ := by
  obtain ⟨h0, h1⟩ := atomPairCodeState.correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne k n hk
  obtain ⟨h0', h1'⟩ := atomPairCodeState.correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne k' n hk'
  rw [h0, h0', h1, h1']
  exact atomPairG.disjoint D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit
    P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair k) (deltaPair k') n hne

end atomPairCodeState
namespace atomPairG
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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in

theorem fst_eq_empty_of_junk_eq_one (i : ℕ) : ∀ n,
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 →
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 = ∅ := by
  intro n
  induction n with
  | zero =>
    intro h
    exfalso
    have h0 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 i = 0 := by
      simp [atomPairJunk, atomPairCodeState, atomPairBase, stateBase2]
    omega
  | succ n ih =>
    intro hjunk1
    rcases Nat.eq_zero_or_pos (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      with hn0 | hnpos
    ·
      obtain ⟨hidx0, hidx1⟩ := atomPairCodeState.correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n
        hn0
      unfold atomPairJunk at hjunk1 hn0
      unfold atomPairIdx0 at hidx0
      unfold atomPairIdx1 at hidx1
      rw [atomPairCodeState.succ] at hjunk1
      unfold atomPairStep pcN pcT xwB1 xwS at hjunk1
      simp only [unpair_pair_fst, unpair_pair_snd, stateInnerC_packStateC] at hjunk1 hidx0 hidx1
      set T := atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (Nat.pair i n)
        with hTdef
      have hrem : stateRemC T = i / 4 ^ n :=
        stateRemC.atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
      have hb1 : stateRemC T % 2 = if (deltaPair i n).1 then 1 else 0 := by
        rw [hrem]
        rcases Nat.mod_two_eq_zero_or_one (i / 4 ^ n) with h0 | h1
        · have hδ : (deltaPair i n).1 = false := by unfold deltaPair; simp [h0]
          simp [hδ, h0]
        · have hδ : (deltaPair i n).1 = true := by unfold deltaPair; simp [h1]
          simp [hδ, h1]
      have hb2 : stateRemC T / 2 % 2 = if (deltaPair i n).2 then 1 else 0 := by
        rw [hrem]
        rcases Nat.mod_two_eq_zero_or_one (i / 4 ^ n / 2) with h0 | h1
        · have hδ : (deltaPair i n).2 = false := by unfold deltaPair; simp [h0]
          simp [hδ, h0]
        · have hδ : (deltaPair i n).2 = true := by unfold deltaPair; simp [h1]
          simp [hδ, h1]
      rw [hb1, hb2] at hjunk1
      rw [ySubStep.junk_eq] at hjunk1
      rw [xSubStep.junk_eq, hn0, selectFn_zero] at hjunk1
      have hb1le : (if (deltaPair i n).1 then (1 : ℕ) else 0) ≤ 1 := by
        rcases Bool.eq_false_or_eq_true (deltaPair i n).1 with h | h <;> simp [h]
      have hxle : selectFn (if (deltaPair i n).1 then 1 else 0)
          (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
          (IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n)) ≤ 1 :=
        selectFn.le_one hb1le (emptyInterDec.le_one P₀ _) (IsComputableDiff.emptyDiffDec.le_one P₀ hDiff0 _)
      rcases Nat.eq_zero_or_pos (selectFn (if (deltaPair i n).1 then 1 else 0)
          (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
          (IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n))) with hx0 | hxpos
      ·
        rw [hx0, selectFn_zero] at hjunk1
        have hxnonjunk : stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX
            (Nat.pair n (Nat.pair (if (deltaPair i n).1 then 1 else 0) (stateInnerC T)))) = 0 := by
          rw [xSubStep.junk_eq, hn0, selectFn_zero]; exact hx0
        obtain ⟨ihAB, -, ihB⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
        obtain ⟨hxA1, hxB1⟩ := xSubStep.correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin
          hxSplit hidx0 hidx1 ihAB ihB (deltaPair i n).1 hxnonjunk
        have hB2 : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) (n + 1)).2 = ∅ := by
          rw [atomPairG.succ_eq]
          by_cases hδ2 : (deltaPair i n).2 = true
          · simp only [hδ2, ite_true] at hjunk1
            rw [selectFn_one] at hjunk1
            have hBe := (emptyInterDec.eq_one_iff P₁ hD₁pos hD₁nomin _ _).mp hjunk1
            rw [hxB1] at hBe
            simp only [yStepG, xyStep, Prod.swap, hδ2, ite_true]
            exact hBe
          · simp only [hδ2, Bool.false_eq_true, ite_false] at hjunk1
            rw [selectFn_zero] at hjunk1
            have hBe := (IsComputableDiff.emptyDiffDec.eq_one_iff P₁ hDiff1 hD₁diff hD₁nomin _ _).mp hjunk1
            rw [hxB1] at hBe
            simp only [yStepG, xyStep, Prod.swap, hδ2, Bool.false_eq_true, ite_false]
            exact hBe
        exact (atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX
          hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) (n + 1)).1.mpr hB2
      ·
        have hx1 : selectFn (if (deltaPair i n).1 then 1 else 0)
            (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
            (IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n)) = 1 := by omega
        have hA1eq : (xStepG splitX
            (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
            (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n)
            (deltaPair i n).1).1 = ∅ := by
          by_cases hδ1 : (deltaPair i n).1 = true
          · simp only [xStepG, xyStep, hδ1, ite_true] at hx1 ⊢
            rw [selectFn_one] at hx1
            have hAe := (emptyInterDec.eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp hx1
            rw [hidx0] at hAe
            exact hAe
          · simp only [xStepG, xyStep, hδ1, Bool.false_eq_true, ite_false] at hx1 ⊢
            rw [selectFn_zero] at hx1
            have hAe := (IsComputableDiff.emptyDiffDec.eq_one_iff P₀ hDiff0 hD₀diff hD₀nomin _ _).mp hx1
            rw [hidx0] at hAe
            exact hAe
        obtain ⟨hspecAB, hspecAmem⟩ := xStepG.spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
        rw [atomPairG.succ_eq]
        exact Set.subset_eq_empty
          (yStepG.fst_subset hySplit hspecAB hspecAmem (P₁.X n) (deltaPair i n).2) hA1eq
    ·
      have hn1 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 := by
        have := atomPairJunk.le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
        omega
      exact Set.subset_eq_empty (atomPairG.fst_subset D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
        hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n) (ih hn1)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in

theorem snd_eq_empty_of_junk_eq_one (i : ℕ) : ∀ n,
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 →
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 = ∅ := by
  intro n
  induction n with
  | zero =>
    intro h
    exfalso
    have h0 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY 0 i = 0 := by
      simp [atomPairJunk, atomPairCodeState, atomPairBase, stateBase2]
    omega
  | succ n ih =>
    intro hjunk1
    rcases Nat.eq_zero_or_pos (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
      with hn0 | hnpos
    ·
      obtain ⟨hidx0, hidx1⟩ := atomPairCodeState.correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n
        hn0
      unfold atomPairJunk at hjunk1 hn0
      unfold atomPairIdx0 at hidx0
      unfold atomPairIdx1 at hidx1
      rw [atomPairCodeState.succ] at hjunk1
      unfold atomPairStep pcN pcT xwB1 xwS at hjunk1
      simp only [unpair_pair_fst, unpair_pair_snd, stateInnerC_packStateC] at hjunk1 hidx0 hidx1
      set T := atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY (Nat.pair i n)
        with hTdef
      have hrem : stateRemC T = i / 4 ^ n :=
        stateRemC.atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
      have hb1 : stateRemC T % 2 = if (deltaPair i n).1 then 1 else 0 := by
        rw [hrem]
        rcases Nat.mod_two_eq_zero_or_one (i / 4 ^ n) with h0 | h1
        · have hδ : (deltaPair i n).1 = false := by unfold deltaPair; simp [h0]
          simp [hδ, h0]
        · have hδ : (deltaPair i n).1 = true := by unfold deltaPair; simp [h1]
          simp [hδ, h1]
      have hb2 : stateRemC T / 2 % 2 = if (deltaPair i n).2 then 1 else 0 := by
        rw [hrem]
        rcases Nat.mod_two_eq_zero_or_one (i / 4 ^ n / 2) with h0 | h1
        · have hδ : (deltaPair i n).2 = false := by unfold deltaPair; simp [h0]
          simp [hδ, h0]
        · have hδ : (deltaPair i n).2 = true := by unfold deltaPair; simp [h1]
          simp [hδ, h1]
      rw [hb1, hb2] at hjunk1
      rw [ySubStep.junk_eq] at hjunk1
      rw [xSubStep.junk_eq, hn0, selectFn_zero] at hjunk1
      have hb1le : (if (deltaPair i n).1 then (1 : ℕ) else 0) ≤ 1 := by
        rcases Bool.eq_false_or_eq_true (deltaPair i n).1 with h | h <;> simp [h]
      have hxle : selectFn (if (deltaPair i n).1 then 1 else 0)
          (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
          (IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n)) ≤ 1 :=
        selectFn.le_one hb1le (emptyInterDec.le_one P₀ _) (IsComputableDiff.emptyDiffDec.le_one P₀ hDiff0 _)
      rcases Nat.eq_zero_or_pos (selectFn (if (deltaPair i n).1 then 1 else 0)
          (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
          (IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n))) with hx0 | hxpos
      ·
        rw [hx0, selectFn_zero] at hjunk1
        have hxnonjunk : stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX
            (Nat.pair n (Nat.pair (if (deltaPair i n).1 then 1 else 0) (stateInnerC T)))) = 0 := by
          rw [xSubStep.junk_eq, hn0, selectFn_zero]; exact hx0
        obtain ⟨ihAB, -, ihB⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
        obtain ⟨-, hxB1⟩ := xSubStep.correct P₀ P₁ hDiff0 splitX hSplitX hD₀pos hD₀diff hD₀nomin
          hxSplit hidx0 hidx1 ihAB ihB (deltaPair i n).1 hxnonjunk
        rw [atomPairG.succ_eq]
        by_cases hδ2 : (deltaPair i n).2 = true
        · simp only [hδ2, ite_true] at hjunk1
          rw [selectFn_one] at hjunk1
          have hBe := (emptyInterDec.eq_one_iff P₁ hD₁pos hD₁nomin _ _).mp hjunk1
          rw [hxB1] at hBe
          simp only [yStepG, xyStep, Prod.swap, hδ2, ite_true]
          exact hBe
        · simp only [hδ2, Bool.false_eq_true, ite_false] at hjunk1
          rw [selectFn_zero] at hjunk1
          have hBe := (IsComputableDiff.emptyDiffDec.eq_one_iff P₁ hDiff1 hD₁diff hD₁nomin _ _).mp hjunk1
          rw [hxB1] at hBe
          simp only [yStepG, xyStep, Prod.swap, hδ2, Bool.false_eq_true, ite_false]
          exact hBe
      ·
        have hx1 : selectFn (if (deltaPair i n).1 then 1 else 0)
            (emptyInterDec P₀ (Nat.pair (stateIdx0 (stateInnerC T)) n))
            (IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (stateIdx0 (stateInnerC T)) n)) = 1 := by omega
        have hA1eq : (xStepG splitX
            (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1
            (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 (P₀.X n)
            (deltaPair i n).1).1 = ∅ := by
          by_cases hδ1 : (deltaPair i n).1 = true
          · simp only [xStepG, xyStep, hδ1, ite_true] at hx1 ⊢
            rw [selectFn_one] at hx1
            have hAe := (emptyInterDec.eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp hx1
            rw [hidx0] at hAe
            exact hAe
          · simp only [xStepG, xyStep, hδ1, Bool.false_eq_true, ite_false] at hx1 ⊢
            rw [selectFn_zero] at hx1
            have hAe := (IsComputableDiff.emptyDiffDec.eq_one_iff P₀ hDiff0 hD₀diff hD₀nomin _ _).mp hx1
            rw [hidx0] at hAe
            exact hAe
        obtain ⟨hspecAB, -⟩ := xStepG.spec D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
          hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n
        rw [atomPairG.succ_eq]
        exact Set.subset_eq_empty
          (yStepG.snd_subset splitY _ _ (P₁.X n) (deltaPair i n).2) (hspecAB.mpr hA1eq)
    ·
      have hn1 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 := by
        have := atomPairJunk.le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
        omega
      exact Set.subset_eq_empty (atomPairG.snd_subset D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos
        hD₁diff splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair i) n) (ih hn1)

end atomPairG

namespace atomPairJunk
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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in

theorem eq_zero_of_snd_ne_empty {i n : ℕ}
    (h : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).2 ≠ ∅) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 := by
  by_contra hne
  have h1 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 := by
    have := atomPairJunk.le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
    omega
  exact h (atomPairG.snd_eq_empty_of_junk_eq_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n h1)

end atomPairJunk
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718


namespace atomPairJunk
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

theorem eq_zero_of_yPseqAtomJunk {n i : ℕ} (b : Bool)
    (hjunk : yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i
      (if b then 1 else 0) = 0) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 := by
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
    rw [ySubStep.junk_eq, selectFn_one] at h2
    exact junk_eq_zero_of_selectFn_eq_zero h2
  have h3 := hxnonjunk
  rw [hs1def, xSubStep.junk_eq, hs0def, stateJunk_packState2] at h3
  exact junk_eq_zero_of_selectFn_eq_zero h3

end YPseqCodeIFormula

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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in

theorem eq_zero_of_ne_empty {i n : ℕ}
    (h : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair i) n).1 ≠ ∅) :
    atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0 := by
  by_contra hne
  have h1 : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 1 := by
    have := atomPairJunk.le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY i n
    omega
  exact h (atomPairG.fst_eq_empty_of_junk_eq_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
    hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne i n h1)

end atomPairJunk

end DomainTheory.NeighbourhoodSystems
