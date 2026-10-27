module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.domainIso812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomE
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.xStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.yStepG
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomPairG
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.combinedCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

namespace primrec
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem stateIdx0 : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.stateIdx0 := Nat.Primrec.left

theorem stateIdx1 : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.stateIdx1 := Nat.Primrec.left.comp Nat.Primrec.right

theorem stateJunk : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.stateJunk := Nat.Primrec.right.comp Nat.Primrec.right

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem atomPairBase : Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.atomPairBase P₀ P₁) :=
  (Nat.Primrec.id.pair (Nat.Primrec.const (stateBase2 P₀.masterIdx P₁.masterIdx))).of_eq
    fun k => by unfold _root_.DomainTheory.NeighbourhoodSystems.atomPairBase packStateC; simp only [id_eq]

end AtomPairCode

theorem IsComputableUnion.combineFound2 {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) :
    Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.IsComputableUnion.combineFound2 hUnion t.unpair.1 t.unpair.2) := by
  have h0 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have h1 : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hf0 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) := Nat.Primrec.left.comp h0
  have hf1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp h1
  have hv0 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) := Nat.Primrec.right.comp h0
  have hv1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp h1
  have hunion : Nat.Primrec
      (fun t : ℕ => hUnion.unionIdx t.unpair.1.unpair.2 t.unpair.2.unpair.2) :=
    (hUnion.unionIdx_primrec.comp (hv0.pair hv1)).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hinner : Nat.Primrec (fun t : ℕ => selectFn t.unpair.2.unpair.1
      (Nat.pair 1 (hUnion.unionIdx t.unpair.1.unpair.2 t.unpair.2.unpair.2)) t.unpair.1) :=
    primrec_selectFn hf1 ((Nat.Primrec.const 1).pair hunion) h0
  exact (primrec_selectFn hf0 hinner h1).of_eq fun t => by unfold _root_.DomainTheory.NeighbourhoodSystems.IsComputableUnion.combineFound2; simp only []

theorem stateInnerC : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.stateInnerC := Nat.Primrec.right

theorem stateRemC : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.stateRemC := Nat.Primrec.left

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

theorem xwB1 : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xwB1 := Nat.Primrec.left.comp Nat.Primrec.right

end XSubStep

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem pcN : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.pcN := primrec.xwB1

end AtomPairCode

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

theorem xwN : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xwN := Nat.Primrec.left

theorem xwS : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xwS := Nat.Primrec.right.comp Nat.Primrec.right

end XSubStep

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem pcT : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.pcT := primrec.xwS

end AtomPairCode

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

theorem xSubStep : Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.xSubStep P₀ P₁ hDiff0 splitX hSplitX) := by
  have hn : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xwN := primrec.xwN
  have hb1 : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xwB1 := primrec.xwB1
  have hs : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xwS := primrec.xwS
  have hidx0 : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) := primrec.stateIdx0.comp hs
  have hidx1 : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) := primrec.stateIdx1.comp hs
  have hjunk : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) := primrec.stateJunk.comp hs
  have hinter : Nat.Primrec (fun w => P₀.inter (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)) :=
    (P₀.inter_primrec.comp (hidx0.pair hn)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hdiffidx : Nat.Primrec (fun w => hDiff0.diffIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)) :=
    (hDiff0.diffIdx_primrec.comp (hidx0.pair hn)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hemptyInter : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₀ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))) :=
    (primrec.emptyInterDec P₀).comp (hidx0.pair hn)
  have hemptyDiff : Nat.Primrec
      (fun w => _root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))) :=
    (IsComputableDiff.primrec.emptyDiffDec P₀ hDiff0).comp (hidx0.pair hn)
  have hposIdx : Nat.Primrec
      (fun w => hSplitX.posIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)) :=
    (hSplitX.posIdx_primrec.comp (hidx0.pair (hidx1.pair hn))).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hnegIdx : Nat.Primrec
      (fun w => hSplitX.negIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)) :=
    (hSplitX.negIdx_primrec.comp (hidx0.pair (hidx1.pair hn))).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hdirectIdx : Nat.Primrec (fun w => selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (P₀.inter (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)) (hDiff0.diffIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))) :=
    primrec_selectFn hb1 hinter hdiffidx
  have hdirectEmpty : Nat.Primrec (fun w => selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₀ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))) :=
    primrec_selectFn hb1 hemptyInter hemptyDiff
  have hsplitIdx : Nat.Primrec (fun w => selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (hSplitX.posIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))
      (hSplitX.negIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))) :=
    primrec_selectFn hb1 hposIdx hnegIdx
  have hnewJunk : Nat.Primrec (fun w => selectFn (_root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) 1 (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₀ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))))) :=
    primrec_selectFn hjunk (Nat.Primrec.const 1) hdirectEmpty
  have hidx0' : Nat.Primrec (fun w => selectFn (selectFn (_root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) 1 (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₀ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))))) 0
      (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w) (P₀.inter (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))
        (hDiff0.diffIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hdirectIdx
  have hidx1' : Nat.Primrec (fun w => selectFn (selectFn (_root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) 1 (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₀ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P₀ hDiff0 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))))) 0
      (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w) (hSplitX.posIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))
        (hSplitX.negIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hsplitIdx
  exact (hidx0'.pair (hidx1'.pair hnewJunk)).of_eq fun w => by
    unfold _root_.DomainTheory.NeighbourhoodSystems.xSubStep packState2
    simp only []

end XSubStep

section YSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff1 : IsComputableDiff P₁)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem ySubStep : Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.ySubStep P₀ P₁ hDiff1 splitY hSplitY) := by
  have hn : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xwN := primrec.xwN
  have hb2 : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xwB1 := primrec.xwB1
  have hs : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xwS := primrec.xwS
  have hidx0 : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) := primrec.stateIdx0.comp hs
  have hidx1 : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) := primrec.stateIdx1.comp hs
  have hjunk : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) := primrec.stateJunk.comp hs
  have hinter : Nat.Primrec (fun w => P₁.inter (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)) :=
    (P₁.inter_primrec.comp (hidx1.pair hn)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hdiffidx : Nat.Primrec (fun w => hDiff1.diffIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)) :=
    (hDiff1.diffIdx_primrec.comp (hidx1.pair hn)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hemptyInter : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₁ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))) :=
    (primrec.emptyInterDec P₁).comp (hidx1.pair hn)
  have hemptyDiff : Nat.Primrec
      (fun w => _root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P₁ hDiff1 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))) :=
    (IsComputableDiff.primrec.emptyDiffDec P₁ hDiff1).comp (hidx1.pair hn)
  have hposIdx : Nat.Primrec
      (fun w => hSplitY.posIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)) :=
    (hSplitY.posIdx_primrec.comp (hidx1.pair (hidx0.pair hn))).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hnegIdx : Nat.Primrec
      (fun w => hSplitY.negIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)) :=
    (hSplitY.negIdx_primrec.comp (hidx1.pair (hidx0.pair hn))).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hdirectIdx : Nat.Primrec (fun w => selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (P₁.inter (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)) (hDiff1.diffIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))) :=
    primrec_selectFn hb2 hinter hdiffidx
  have hdirectEmpty : Nat.Primrec (fun w => selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₁ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P₁ hDiff1 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))) :=
    primrec_selectFn hb2 hemptyInter hemptyDiff
  have hsplitIdx : Nat.Primrec (fun w => selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (hSplitY.posIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))
      (hSplitY.negIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))) :=
    primrec_selectFn hb2 hposIdx hnegIdx
  have hnewJunk : Nat.Primrec (fun w => selectFn (_root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) 1 (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₁ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P₁ hDiff1 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))))) :=
    primrec_selectFn hjunk (Nat.Primrec.const 1) hdirectEmpty
  have hidx0' : Nat.Primrec (fun w => selectFn (selectFn (_root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) 1 (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₁ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P₁ hDiff1 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))))) 0
      (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w) (hSplitY.posIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))
        (hSplitY.negIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hsplitIdx
  have hidx1' : Nat.Primrec (fun w => selectFn (selectFn (_root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) 1 (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₁ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.IsComputableDiff.emptyDiffDec P₁ hDiff1 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))))) 0
      (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w) (P₁.inter (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))
        (hDiff1.diffIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hdirectIdx
  exact (hidx0'.pair (hidx1'.pair hnewJunk)).of_eq fun w => by
    unfold _root_.DomainTheory.NeighbourhoodSystems.ySubStep packState2
    simp only []

end YSubStep

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem atomPairStep :
    Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.atomPairStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY) := by
  have hy : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.pcN := primrec.pcN
  have hst : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.pcT := primrec.pcT
  have hrem : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.stateRemC (_root_.DomainTheory.NeighbourhoodSystems.pcT w)) := primrec.stateRemC.comp hst
  have hs : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.stateInnerC (_root_.DomainTheory.NeighbourhoodSystems.pcT w)) := primrec.stateInnerC.comp hst
  have hb1 : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.stateRemC (_root_.DomainTheory.NeighbourhoodSystems.pcT w) % 2) := primrec_mod2.comp hrem
  have hb2 : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.stateRemC (_root_.DomainTheory.NeighbourhoodSystems.pcT w) / 2 % 2) :=
    primrec_mod2.comp (primrec_div2.comp hrem)
  have hw1 : Nat.Primrec (fun w => Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.pcN w) (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateRemC (_root_.DomainTheory.NeighbourhoodSystems.pcT w) % 2)
      (_root_.DomainTheory.NeighbourhoodSystems.stateInnerC (_root_.DomainTheory.NeighbourhoodSystems.pcT w)))) := hy.pair (hb1.pair hs)
  have hs1 : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.xSubStep P₀ P₁ hDiff0 splitX hSplitX
      (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.pcN w) (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateRemC (_root_.DomainTheory.NeighbourhoodSystems.pcT w) % 2) (_root_.DomainTheory.NeighbourhoodSystems.stateInnerC (_root_.DomainTheory.NeighbourhoodSystems.pcT w))))) :=
    (primrec.xSubStep P₀ P₁ hDiff0 splitX hSplitX).comp hw1
  have hw2 : Nat.Primrec (fun w => Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.pcN w) (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateRemC (_root_.DomainTheory.NeighbourhoodSystems.pcT w) / 2 % 2)
      (_root_.DomainTheory.NeighbourhoodSystems.xSubStep P₀ P₁ hDiff0 splitX hSplitX
        (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.pcN w) (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateRemC (_root_.DomainTheory.NeighbourhoodSystems.pcT w) % 2) (_root_.DomainTheory.NeighbourhoodSystems.stateInnerC (_root_.DomainTheory.NeighbourhoodSystems.pcT w))))))) :=
    hy.pair (hb2.pair hs1)
  have hs2 : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.ySubStep P₀ P₁ hDiff1 splitY hSplitY
      (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.pcN w) (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateRemC (_root_.DomainTheory.NeighbourhoodSystems.pcT w) / 2 % 2)
        (_root_.DomainTheory.NeighbourhoodSystems.xSubStep P₀ P₁ hDiff0 splitX hSplitX
          (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.pcN w) (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateRemC (_root_.DomainTheory.NeighbourhoodSystems.pcT w) % 2) (_root_.DomainTheory.NeighbourhoodSystems.stateInnerC (_root_.DomainTheory.NeighbourhoodSystems.pcT w)))))))) :=
    (primrec.ySubStep P₀ P₁ hDiff1 splitY hSplitY).comp hw2
  have hrem' : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.stateRemC (_root_.DomainTheory.NeighbourhoodSystems.pcT w) / 4) := by
    have : Nat.Primrec (fun w => _root_.DomainTheory.NeighbourhoodSystems.stateRemC (_root_.DomainTheory.NeighbourhoodSystems.pcT w) / 2 / 2) :=
      primrec_div2.comp (primrec_div2.comp hrem)
    exact this.of_eq fun w => by rw [Nat.div_div_eq_div_mul]
  exact (hrem'.pair hs2).of_eq fun w => by
    unfold _root_.DomainTheory.NeighbourhoodSystems.atomPairStep packStateC
    simp only []

theorem atomPairCodeState :
    Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY) :=
  (Nat.Primrec.prec (primrec.atomPairBase P₀ P₁)
    (primrec.atomPairStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY)).of_eq fun _ => rfl

theorem atomPairIdx0 : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
  (primrec.stateIdx0.comp (primrec.stateInnerC.comp
    ((primrec.atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp
      (Nat.Primrec.right.pair Nat.Primrec.left)))).of_eq fun _ => rfl

theorem atomPairIdx1 : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
  (primrec.stateIdx1.comp (primrec.stateInnerC.comp
    ((primrec.atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp
      (Nat.Primrec.right.pair Nat.Primrec.left)))).of_eq fun _ => rfl

theorem atomPairJunk : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
  (primrec.stateJunk.comp (primrec.stateInnerC.comp
    ((primrec.atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp
      (Nat.Primrec.right.pair Nat.Primrec.left)))).of_eq fun _ => rfl

end AtomPairCode

end primrec

end DomainTheory.NeighbourhoodSystems
