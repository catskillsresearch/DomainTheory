module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.XPseqCode_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812d_early

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace xPseqAtomIdx
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XPseqCodeIFormula

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
  (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 800000 in

theorem subset_atomPairIdx1 {n m : ℕ}
    (hjunk : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m = 0) :
    P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m) ⊆
      P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m) := by
  have hraw := hjunk
  rw [xPseqAtomJunk.eq] at hraw
  obtain ⟨hAjunk, hempty0⟩ := selectFn.one_eq_zero_iff.mp hraw
  have hidxeq := xPseqAtomIdx.eq P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hjunk
  have hcs := atomPairCodeState.correct P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne m n hAjunk
  have hinv := atomPairG.invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit
    P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne (deltaPair m) n
  have hspec := hxSplit hinv.1 hinv.2.2 (P₀.X n)
  have hne : (splitX (P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m))
      (P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m)) (P₀.X n)).1 ≠
      ∅ := by
    rw [hcs.1, hcs.2]
    have hempty' : P₀.X (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m) ∩
        P₀.X n ≠ ∅ := (emptyInterDec.eq_one_iff P₀ hD₀pos hD₀nomin _ _).not.mp (by omega)
    rw [hcs.1] at hempty'
    exact hspec.2.2.1.not.mp hempty'
  have hposspec := hSplitX.posIdx_spec
    (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m)
    (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n m) n hne
  rw [hcs.1, hcs.2] at hposspec
  rw [hidxeq, ← hposspec, hcs.2]
  calc (splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).2 (P₀.X n)).1
      ⊆ (splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).2 (P₀.X n)).1 ∪
        (splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).2 (P₀.X n)).2 :=
        Set.subset_union_left
    _ = (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X (deltaPair m) n).2 := hspec.2.2.2.2.1

end XPseqCodeIFormula

section XPseqCodeIFormula

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
  (hUnion1 : IsComputableUnion P₁)

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 800000 in

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 800000 in

theorem eq_inter_XPseqCode {n k : ℕ} (hk : k < 4 ^ n)
    (hjunk : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0) :
    P₁.X (xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) =
      P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k) ∩
        P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 n) := by
  apply Set.Subset.antisymm
  · intro z hz
    refine ⟨xPseqAtomIdx.subset_atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hjunk hz, ?_⟩
    exact (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 n z).mpr
      ⟨k, hk, hjunk, hz⟩
  · rintro z ⟨hzB, hzXP⟩
    obtain ⟨k', hk', hjunk', hz'⟩ := (mem_XPseqCode_iff_unconditional P₀ P₁ hDiff0 hDiff1 splitX
      hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne
      hD₁mne hUnion1 n z).mp hzXP
    by_cases hkk' : k' = k
    · rwa [hkk'] at hz'
    · exfalso
      have hAjunk : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k = 0 := by
        have h := hjunk
        rw [xPseqAtomJunk.eq] at h
        exact junk_eq_zero_of_selectFn_eq_zero h
      have hAjunk' : atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k' = 0 := by
        have h := hjunk'
        rw [xPseqAtomJunk.eq] at h
        exact junk_eq_zero_of_selectFn_eq_zero h
      obtain ⟨i, hi, hne⟩ := deltaPair.exists_ne_of_lt_of_ne hk' hk hkk'
      have hdisj := (atomPairCodeState.disjoint P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        (n := n) (k := k') (k' := k) hAjunk' hAjunk ⟨i, hi, hne⟩).2
      have hz'' : z ∈ P₁.X (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n k') :=
        xPseqAtomIdx.subset_atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
          hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hjunk' hz'
      exact absurd (Set.mem_inter hz'' hzB) (by rw [hdisj]; simp)

end XPseqCodeIFormula

end xPseqAtomIdx

end DomainTheory.NeighbourhoodSystems
