/-ai
If the second component of an atom pair at depth n agrees with the generated atom of combinedYCode at the even depth 2n, then the generated atom at depth 2n+1 equals the second output of the corresponding X-substep.

Rewrite the successor of the generated atom by that even-depth agreement, the even interleaving of the sign, and the even case of combinedYCode. The result is the symmetric form of the closed form for the second output of the X-substep.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combinedYCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combinedYCode_even
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xStepG_snd_succ_eq_XPseqCode

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 in
set_option maxHeartbeats 4000000 in
/-- **The odd-depth half-step identity for `combinedYCode`**, code-level analogue of
`Exercise812c.lean`'s `genAtom_combinedY_succ_eq`: given `atomPairG δ n`'s `β`-side agrees with
`genAtom combinedYCode` at the even depth `2 * n`, it also agrees at the odd depth `2 * n + 1` with
the `X`-sub-step's own direct-refine `β`-side output, via `xStepG_snd_succ_eq_XPseqCode`. -/
theorem genAtom_combinedYCode_succ_eq (δ : ℕ → Bool × Bool) (n : ℕ)
    (hn : (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 =
      genAtom (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
        (combinedδ δ) (2 * n)) :
    genAtom (combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) D₁.master
        (combinedδ δ) (2 * n + 1) =
      (xStepG splitX (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).1
        (atomPairG D₀ D₁ splitY splitX P₀.X P₁.X δ n).2 (P₀.X n) (δ n).1).2 := by
  rw [genAtom_succ', ← hn, combinedδ_even, combinedYCode_even]
  exact (xStepG_snd_succ_eq_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion1 δ n (δ n).1).symm

end CombinedCode

end DomainTheory.NeighbourhoodSystems
