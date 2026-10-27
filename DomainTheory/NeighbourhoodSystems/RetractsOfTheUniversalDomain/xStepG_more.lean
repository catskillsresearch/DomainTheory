module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xPseqAtomIdx_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812d_early
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPairG_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.XPseqCode_more

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace xStepG
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section CombinedCode

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
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 1000000 in

theorem snd_eq_inter_XPseqCode (δ : ℕ → Bool × Bool) (n : ℕ) :
    (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) true).2 =
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 ∩
        P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) := by
  simp only [xStepG, xyStep, ite_true]
  set k := encodeDeltaPair δ n with hkdef
  have hklt : k < 4 ^ n := encodeDeltaPair.lt δ n
  have hagree : ∀ i < n, δ i = deltaPair k i := fun i hi =>
    (deltaPair.encodeDeltaPair δ n i hi).symm
  have hcongr : atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n =
      atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n :=
    atomPairG.congr D₀ D₁ splitY splitX P₀.X P₁.X hagree
  rw [hcongr]
  set A := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair k) n).2 with hBdef
  obtain ⟨hAB, -, hBmem⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair k) n
  rw [← hAdef] at hAB
  rw [← hBdef] at hAB hBmem
  by_cases hB : B = ∅
  · have hspec := hxSplit hAB (Or.inl hB) (P₀.X n)
    have hunion := hspec.2.2.2.2.1
    have h1empty : (splitX A B (P₀.X n)).1 = ∅ :=
      Set.subset_eq_empty Set.subset_union_left (hunion.trans hB)
    rw [h1empty, hB]; simp
  · have hAjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0 :=
      atomPairJunk.eq_zero_of_snd_ne_empty P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
        hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hB
    have hcs := atomPairCodeState.correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne k n hAjunk
    by_cases hxj : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0
    · have hIF := xPseqAtomIdx.eq_inter_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 hklt
        hxj
      have hidxeq := xPseqAtomIdx.eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hxj
      have hraw' := hxj
      rw [xPseqAtomJunk.eq] at hraw'
      obtain ⟨-, hempty0'⟩ := selectFn.one_eq_zero_iff.mp hraw'
      have hAeq : A = P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) :=
        hAdef.trans hcs.1.symm
      have hempty'' : A ∩ P₀.X n ≠ ∅ := by
        rw [hAeq]
        exact (emptyInterDec.eq_one_iff P₀ hD₀pos hD₀nomin _ _).not.mp (by omega)
      have hne : (splitX A B (P₀.X n)).1 ≠ ∅ := by
        have hspecAB := hxSplit hAB hBmem (P₀.X n)
        exact hspecAB.2.2.1.not.mp hempty''
      have hposspec := hSplitX.posIdx_spec
        (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) n
        (by rw [hcs.1, hcs.2]; exact hne)
      rw [hcs.1, hcs.2] at hposspec
      have hgoal2 : P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) =
          (splitX A B (P₀.X n)).1 := by rw [hidxeq]; exact hposspec.symm
      rw [← hgoal2, hIF, hcs.2]
    · have hxj1 : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 1 := by
        have := xPseqAtomJunk.le_one P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k
        omega
      have h2empty : (splitX A B (P₀.X n)).1 = ∅ := by
        have h := hxj1
        rw [xPseqAtomJunk.eq, hAjunk, selectFn_zero] at h
        have hempty := (emptyInterDec.eq_one_iff P₀ hD₀pos hD₀nomin _ _).mp h
        rw [hcs.1] at hempty
        have hspec := hxSplit hAB hBmem (P₀.X n)
        exact hspec.2.2.1.mp hempty
      have hdisjXP : B ∩
          P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨hzB, hzXP⟩
        obtain ⟨k', hk'lt, hjunk', hz'⟩ := (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1
          splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin
          hySplit hD₀mne hD₁mne hUnion1 n z).mp hzXP
        have hkk' : k' ≠ k := by rintro rfl; omega
        have hAjunk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k' = 0 := by
          have h := hjunk'
          rw [xPseqAtomJunk.eq] at h
          exact junk_eq_zero_of_selectFn_eq_zero h
        have hz'' : z ∈ P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k') :=
          xPseqAtomIdx.subset_atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
            hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hjunk' hz'
        have hzB' : z ∈ P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) :=
          hcs.2 ▸ hzB
        obtain ⟨i, hi, hne⟩ := deltaPair.exists_ne_of_lt_of_ne hklt hk'lt hkk'.symm
        have hdisj := (atomPairCodeState.disjoint P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
          hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
          (n := n) (k := k) (k' := k') hAjunk hAjunk' ⟨i, hi, hne⟩).2
        exact absurd (Set.mem_inter hzB' hz'') (by rw [hdisj]; simp)
      rw [h2empty, hdisjXP]

end CombinedCode

section CombinedCode

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
  (hUnion0 : IsComputableUnion P₀) (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 1000000 in

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in

theorem snd_succ_eq_XPseqCode (δ : ℕ → Bool × Bool) (n : ℕ) (b : Bool) :
    (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) b).2 =
      (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 ∩
        (if b then P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n)
          else D₁.master \
            P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n)) := by
  obtain ⟨hAB, -, hBmem⟩ := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 with hBdef
  set XP := P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) with hXPdef
  have hspec := hxSplit hAB hBmem (P₀.X n)
  have hIeq : (xStepG splitX A B (P₀.X n) true).2 = B ∩ XP :=
    xStepG.snd_eq_inter_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 δ n
  by_cases hb : b = true
  · rw [hb, ite_eq_left rfl]; exact hIeq
  · rw [Bool.not_eq_true] at hb; subst hb
    rw [ite_eq_right (by simp)]
    have hJeq : (xStepG splitX A B (P₀.X n) false).2 = B \ XP := by
      have hunion :
          (xStepG splitX A B (P₀.X n) true).2 ∪ (xStepG splitX A B (P₀.X n) false).2 = B := by
        simp only [xStepG, xyStep]; exact hspec.2.2.2.2.1
      have hinter :
          (xStepG splitX A B (P₀.X n) true).2 ∩ (xStepG splitX A B (P₀.X n) false).2 = ∅ := by
        simp only [xStepG, xyStep]; exact hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxB : x ∈ B := hunion ▸ Or.inr hxJ
        refine ⟨hxB, fun hxXP => ?_⟩
        have hxI : x ∈ (xStepG splitX A B (P₀.X n) true).2 := hIeq ▸ Set.mem_inter hxB hxXP
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxB, hxnXP⟩
        rw [← hunion] at hxB
        rcases hxB with hxI | hxJ
        · exact absurd (hIeq ▸ hxI : x ∈ B ∩ XP).2 hxnXP
        · exact hxJ
    rw [hJeq]
    have hsub := atomPairG.snd_subset_master D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
      splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

end CombinedCode

end xStepG

end DomainTheory.NeighbourhoodSystems
