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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812d_early
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812d_early_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.combinedCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec812d_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.combinedCode_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Udiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.domainIsoCode812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.toD0Code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.toD1Code
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.combinedCodeCrossFamily
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.transfer
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.hcoreCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yStepG_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yPseqAtomIdx_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xStepG_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xPseqAtomIdx_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.YPseqCode_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.XPseqCode_more

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

def NeighborhoodSystem.UnionClosed {α : Type*} (D : NeighborhoodSystem α) : Prop :=
  ∀ {X Y : Set α}, D.mem X → D.mem Y → D.mem (X ∪ Y)

section InvMapComp812d

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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

theorem invMap_comp_toMap :
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).comp
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)) =
    idMap D₀ := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  show (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).toElementMap
    ((ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0)).toElementMap x) = _
  rw [toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply, toElementMap_idMap]

end InvMapComp812d

section ToMapComp812d

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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

theorem toMap_comp_invMap :
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)).comp
    (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm) =
    idMap D₁ := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_comp]
  show (ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0)).toElementMap
    ((ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
      hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
      hY0).symm).toElementMap y) = _
  rw [toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply, toElementMap_idMap]

end ToMapComp812d

section EffectiveIso812d

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

include hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
  hUnion1 hX0 hY0 in

noncomputable def effectiveIso812d : EffectiveIso P₀ P₁ where
  toMap := ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0)
  invMap := ofIso (domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos
    hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0
    hY0).symm
  toMap_computable := domainIsoCode812d.isComputableMap P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0
    hUnion1 hX0 hY0
  invMap_computable := domainIsoCode812d.symm_isComputableMap P₀ P₁ hDiff0 hDiff1 splitX hSplitX
    splitY hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne
    hUnion0 hUnion1 hX0 hY0
  left_inv := invMap_comp_toMap P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0
  right_inv := toMap_comp_invMap P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff
    hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0

end EffectiveIso812d

section DomainIsoCode812d

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

include hDiff0 hDiff1 hSplitX hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin
  hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0 in

theorem isomorphic_812d : D₀ ≅ᴰ D₁ :=
  ⟨domainIsoCode812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
    hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0⟩

end DomainIsoCode812d

section EffectiveIso812d

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

include hDiff0 hDiff1 hSplitX hSplitY hD₀pos hD₀diff hD₀nomin hxSplit hD₁pos hD₁diff hD₁nomin
  hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0 in

theorem effectivelyIsomorphic_812d : EffectivelyIsomorphic P₀ P₁ :=
  ⟨effectiveIso812d P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hD₀pos hD₀diff hD₀nomin
    hxSplit hD₁pos hD₁diff hD₁nomin hySplit hD₀mne hD₁mne hUnion0 hUnion1 hX0 hY0⟩
end EffectiveIso812d

end

open Domain.Recursive NeighborhoodSystem
