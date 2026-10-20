module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep_junk_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep_idx0_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XYPseqCodeZero

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
  (hX0 : P₀.X 0 = D₀.master) (hY0 : P₁.X 0 = D₁.master)

/-- **The half-step atom's `D₀`-direct-refine index, in closed form, when non-junk**: the
`D₀`-side twin of `xPseqAtomIdx_eq`, reading off `xSubStep`'s *other* output (`stateIdx0`, the
direct `∩`/`\` refinement against `P₀.X n`, rather than `stateIdx1`'s split branch). -/
theorem xPseqAtomIdx0_eq {n i : ℕ}
    (h : xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i = 0) :
    stateIdx0 (xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) =
      P₀.inter (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i) n := by
  have h' : stateJunk (xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair n (Nat.pair 1
      (packState2 (atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
        (atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i)
        (atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY n i))))) = 0 := h
  rw [xSubStep_junk_eq] at h'
  unfold xPseqAtomState
  rw [xSubStep_idx0_eq (h := h'), stateIdx0_packState2, selectFn_one]

end XYPseqCodeZero

end DomainTheory.NeighbourhoodSystems
