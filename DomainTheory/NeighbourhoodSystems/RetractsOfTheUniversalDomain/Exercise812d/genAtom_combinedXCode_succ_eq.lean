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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairG_fst_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combinedXCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combinedXCode_even

@[expose] public section

set_option linter.unusedSectionVars false

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

include hD₀pos hD₀diff hxSplit hD₁pos hD₁diff hySplit hD₀mne hD₁mne in
set_option maxHeartbeats 4000000 in
/-- **The odd-depth half-step identity for `combinedXCode`**, code-level analogue of
`Exercise812c.lean`'s `genAtom_combinedX_succ_eq`: given `atomPairG δ n`'s `α`-side agrees with
`genAtom combinedXCode` at the even depth `2 * n`, it also agrees at the odd depth `2 * n + 1` with
the `X`-sub-step's own split-side output — elementary algebra plus `atomPairG_fst_subset_master`,
no new disjointness content (the `Y`-sub-step closed form `yStepG_fst_succ_eq_YPseqCode` is what
supplies the genuinely new content, used one level up in `atomPairG_fst_eq_genAtomCode`). -/
theorem genAtom_combinedXCode_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ)
    (hn : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1 =
      genAtom (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master
        (combinedδ δ) (2 * n)) :
    genAtom (combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) D₀.master
        (combinedδ δ) (2 * n + 1) =
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) (δ n).1).1 := by
  rw [genAtom_succ', ← hn, combinedδ_even, combinedXCode_even]
  have hAsub : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1 ⊆ D₀.master :=
    atomPairG_fst_subset_master D₀ D₁ hD₀pos hD₀diff splitY hySplit hD₁pos hD₁diff splitX hxSplit
      P₀.X P₁.X P₀.mem_X P₁.mem_X hD₀mne hD₁mne δ n
  simp only [xStepG, xyStep]
  rcases Bool.eq_false_or_eq_true (δ n).1 with hb | hb
  · simp only [hb, ite_true]
  · simp only [hb, Bool.false_eq_true, ite_false]
    exact inter_diff_eq_diff_of_subset hAsub

end CombinedCode

end DomainTheory.NeighbourhoodSystems
