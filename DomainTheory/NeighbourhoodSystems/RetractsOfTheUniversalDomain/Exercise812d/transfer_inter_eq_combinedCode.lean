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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combinedXCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combinedYCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combinedYCode_subset_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.transfer_subset_combinedCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.transfer_double_subset_combinedCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section CombinedCodeTransfer

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
theorem transfer_inter_eq_combinedCode (i j k : ℕ)
    (hi : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ⊆ D₀.master)
    (hk : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆ D₀.master) :
    combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ∩
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j =
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ↔
      combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ∩
          combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j =
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k := by
  have h1 : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ↔
      combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i := by
    have := transfer_subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 k i
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right
        (combinedYCode_subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
          k)] at this
  have h2 : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j ↔
      combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j := by
    have := transfer_subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
      hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 k j
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right
        (combinedYCode_subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
          k)] at this
  have h3 : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ∩
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ↔
      combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ∩
          combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k := by
    have := transfer_double_subset_combinedCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1
      i j k
    rwa [Set.inter_eq_self_of_subset_right hi,
      Set.inter_eq_self_of_subset_right
        (combinedYCode_subset_master P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
          i)] at this
  constructor
  · intro heq
    have hki : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i :=
      heq ▸ Set.inter_subset_left
    have hkj : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j :=
      heq ▸ Set.inter_subset_right
    have hijk : combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 i ∩
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 j ⊆
        combinedXCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mp hijk) (Set.subset_inter (h1.mp hki) (h2.mp hkj))
  · intro heq
    have hki : combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i :=
      heq ▸ Set.inter_subset_left
    have hkj : combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j :=
      heq ▸ Set.inter_subset_right
    have hijk : combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 i ∩
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 j ⊆
        combinedYCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1 k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mpr hijk) (Set.subset_inter (h1.mpr hki) (h2.mpr hkj))

end CombinedCodeTransfer

end DomainTheory.NeighbourhoodSystems
