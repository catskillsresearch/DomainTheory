module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.X_subset_YPseqCode_iff_XPseqCode_subset_Y
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode_subset_X_iff_Y_subset_XPseqCode

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section CombinedCodeCrossFamily

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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 in
/-- **Exercise 8.12(d)(5)(c)(iii), the cross-parity `embed_eq_iff` analogue.** `P₁.X (XPseqCode …
j) = P₁.X k ↔ P₀.X j = P₀.X (YPseqCode … k)`: code-level analogue of `Exercise812c.lean`'s
`XPseq_eq_Y_iff_X_eq_YPseq` — pure packaging of `(c)(i)`/`(c)(ii)` via `Set.Subset.antisymm` in
each direction, no new mathematical content. Needed because `(d)(5)(d)`'s `toD1Code`/`toD0Code`
`up_mem` case must rename a covering witness produced by `P₀.surj`/`P₁.surj` back into the
`XPseqCode`/`YPseqCode` "coordinates" that the filter `x`/`y` actually testifies about. -/
theorem XPseqCode_eq_Y_iff_X_eq_YPseqCode (j k : ℕ) :
    P₁.X (XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j) = P₁.X k ↔
      P₀.X j = P₀.X (YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k) := by
  constructor
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_YPseqCode_iff_XPseqCode_subset_Y P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        hUnion0 hUnion1 j k).mpr h.subset)
      ((YPseqCode_subset_X_iff_Y_subset_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        hUnion0 hUnion1 k j).mpr h.symm.subset)
  · intro h
    exact Set.Subset.antisymm
      ((X_subset_YPseqCode_iff_XPseqCode_subset_Y P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        hUnion0 hUnion1 j k).mp h.subset)
      ((YPseqCode_subset_X_iff_Y_subset_XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
        hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
        hUnion0 hUnion1 k j).mp h.symm.subset)

end CombinedCodeCrossFamily

end DomainTheory.NeighbourhoodSystems
