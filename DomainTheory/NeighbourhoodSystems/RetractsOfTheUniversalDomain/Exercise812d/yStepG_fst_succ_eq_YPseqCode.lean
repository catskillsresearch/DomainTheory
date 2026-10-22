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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG_fst_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_invariant
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_fst_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yStepG_fst_eq_inter_YPseqCode

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union_mem_or_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
set_option maxHeartbeats 4000000 in

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 in
/-- **Two-branch closed form, generalized to an arbitrary `δ`** (not just a bounded bit-source `k <
4 ^ n`): completes `yStepG_fst_eq_inter_YPseqCode`'s `true`-only fact (specialized to the `X`-side
bit `(δ n).1`, exactly as `Exercise812c.lean`'s `yStep_fst_succ_eq` fixes it) into a full
`genAtom`-shaped closed step at *either* sign of the `Y`-sub-step — the `false` branch is derived
algebraically from the `true` branch plus `SplitSpec'`'s `I ∪ J = A1`/`I ∩ J = ∅`, mirroring
`xStepG_snd_succ_eq_XPseqCode` exactly (with the roles of `hySplit`/`hxSplit` swapped). -/
theorem yStepG_fst_succ_eq_YPseqCode (δ : ℕ → Bool × Bool) (n : ℕ) (b : Bool) :
    (yStepG splitY
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) (δ n).1).1
        (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) (δ n).1).2
        (P₁.X n) b).1 =
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
          (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) (δ n).1).1 ∩
        (if b then P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)
          else D₀.master \
            P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n)) := by
  obtain ⟨ihAB, ihA, ihB⟩ := atomPairG_invariant D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff
    splitX hxSplit P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n
  set A := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1 with hAdef
  set B := (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 with hBdef
  set A1 := (xStepG splitX A B (P₀.X n) (δ n).1).1 with hA1def
  set B1 := (xStepG splitX A B (P₀.X n) (δ n).1).2 with hB1def
  set YP := P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n) with hYPdef
  have hspec1 := hxSplit ihAB ihB (P₀.X n)
  have hA1B1 : A1 = ∅ ↔ B1 = ∅ := by
    rw [hA1def, hB1def]
    by_cases hbx : (δ n).1 = true
    · simp only [xStepG, xyStep, hbx, ite_true]; exact hspec1.2.2.1
    · simp only [xStepG, xyStep, hbx, Bool.false_eq_true, ite_false]; exact hspec1.2.2.2.1
  have hA1mem : A1 = ∅ ∨ D₀.mem A1 := by
    rw [hA1def]
    by_cases hbx : (δ n).1 = true
    · simp only [xStepG, xyStep, hbx, ite_true]; exact inter_mem_or_empty hD₀pos ihA (P₀.mem_X n)
    · simp only [xStepG, xyStep, hbx, Bool.false_eq_true, ite_false]
      exact diff_mem_or_empty hD₀diff ihA (P₀.mem_X n)
  have hspec := hySplit hA1B1.symm hA1mem (P₁.X n)
  have hJeqTrue : (yStepG splitY A1 B1 (P₁.X n) true).1 = A1 ∩ YP :=
    yStepG_fst_eq_inter_YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 δ n (δ n).1
  by_cases hb : b = true
  · rw [hb, ite_eq_left rfl]; exact hJeqTrue
  · rw [Bool.not_eq_true] at hb; subst hb
    rw [ite_eq_right (by simp)]
    have hJeq : (yStepG splitY A1 B1 (P₁.X n) false).1 = A1 \ YP := by
      have hunion :
          (yStepG splitY A1 B1 (P₁.X n) true).1 ∪ (yStepG splitY A1 B1 (P₁.X n) false).1 = A1 := by
        simp only [yStepG, xyStep, Prod.swap]; exact hspec.2.2.2.2.1
      have hinter :
          (yStepG splitY A1 B1 (P₁.X n) true).1 ∩ (yStepG splitY A1 B1 (P₁.X n) false).1 = ∅ := by
        simp only [yStepG, xyStep, Prod.swap]; exact hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxA1 : x ∈ A1 := hunion ▸ Or.inr hxJ
        refine ⟨hxA1, fun hxYP => ?_⟩
        have hxI : x ∈ (yStepG splitY A1 B1 (P₁.X n) true).1 := hJeqTrue ▸ Set.mem_inter hxA1 hxYP
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxA1, hxnYP⟩
        rw [← hunion] at hxA1
        rcases hxA1 with hxI | hxJ
        · exact absurd (hJeqTrue ▸ hxI : x ∈ A1 ∩ YP).2 hxnYP
        · exact hxJ
    rw [hJeq]
    have hsub : A1 ⊆ D₀.master := (xStepG_fst_subset splitX A B (P₀.X n) (δ n).1).trans
      (atomPairG_fst_subset_master D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit
        P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n)
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

end CombinedCode

end DomainTheory.NeighbourhoodSystems
