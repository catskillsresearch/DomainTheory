module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.existsDiffDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyDiffDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.existsInterDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.emptyInterDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.combineFound2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_3
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xSubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.ySubStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairCodeState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.atomPairJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.xPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_5
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XFold
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.XPseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.yPseqAtomJunk
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YFoldInner
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.YPseqCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable (hDiff : IsComputableDiff P)

theorem existsDiffDec : Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.existsDiffDec P hDiff) :=
  (primrec_isOne.comp hDiff.diff_computable.choose_spec.1).of_eq fun _ => rfl

end DirectDec

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable (hDiff : IsComputableDiff P)

theorem emptyDiffDec : Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P hDiff) :=
  primrec_sub₂ (Nat.Primrec.const 1) (primrec.existsDiffDec P hDiff)

end DirectDec

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

theorem existsInterDec : Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.existsInterDec P) :=
  (primrec_isOne.comp P.cons_computable.choose_spec.1).of_eq fun _ => rfl

end DirectDec

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

theorem emptyInterDec : Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P) :=
  primrec_sub₂ (Nat.Primrec.const 1) (primrec.existsInterDec P)

end DirectDec

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem stateIdx0 : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.stateIdx0 := Nat.Primrec.left

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem stateIdx1 : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.stateIdx1 := Nat.Primrec.left.comp Nat.Primrec.right

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem stateJunk : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.stateJunk := Nat.Primrec.right.comp Nat.Primrec.right

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

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

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem combineFound2 {γ : Type*} {W : NeighborhoodSystem γ}
    {Q : ComputablePresentation W} (hUnion : IsComputableUnion Q) :
    Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.combineFound2 hUnion t.unpair.1 t.unpair.2) := by
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
  exact (primrec_selectFn hf0 hinner h1).of_eq fun t => by unfold _root_.DomainTheory.NeighbourhoodSystems.combineFound2; simp only []

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem stateInnerC : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.stateInnerC := Nat.Primrec.right

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

theorem stateRemC : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.stateRemC := Nat.Primrec.left

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

theorem xwB1 : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xwB1 := Nat.Primrec.left.comp Nat.Primrec.right

end XSubStep

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem pcN : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.pcN := primrec.xwB1

end AtomPairCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

theorem xwN : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xwN := Nat.Primrec.left

end XSubStep

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section XSubStep

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)

theorem xwS : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.xwS := Nat.Primrec.right.comp Nat.Primrec.right

end XSubStep

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem pcT : Nat.Primrec _root_.DomainTheory.NeighbourhoodSystems.pcT := primrec.xwS

end AtomPairCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

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
      (fun w => _root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P₀ hDiff0 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))) :=
    (primrec.emptyDiffDec P₀ hDiff0).comp (hidx0.pair hn)
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
      (_root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P₀ hDiff0 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))) :=
    primrec_selectFn hb1 hemptyInter hemptyDiff
  have hsplitIdx : Nat.Primrec (fun w => selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (hSplitX.posIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))
      (hSplitX.negIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))) :=
    primrec_selectFn hb1 hposIdx hnegIdx
  have hnewJunk : Nat.Primrec (fun w => selectFn (_root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) 1 (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₀ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P₀ hDiff0 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))))) :=
    primrec_selectFn hjunk (Nat.Primrec.const 1) hdirectEmpty
  have hidx0' : Nat.Primrec (fun w => selectFn (selectFn (_root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) 1 (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₀ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P₀ hDiff0 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))))) 0
      (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w) (P₀.inter (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))
        (hDiff0.diffIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hdirectIdx
  have hidx1' : Nat.Primrec (fun w => selectFn (selectFn (_root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) 1 (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₀ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P₀ hDiff0 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))))) 0
      (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w) (hSplitX.posIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))
        (hSplitX.negIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hsplitIdx
  exact (hidx0'.pair (hidx1'.pair hnewJunk)).of_eq fun w => by
    unfold _root_.DomainTheory.NeighbourhoodSystems.xSubStep packState2
    simp only []

end XSubStep

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

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
      (fun w => _root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P₁ hDiff1 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))) :=
    (primrec.emptyDiffDec P₁ hDiff1).comp (hidx1.pair hn)
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
      (_root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P₁ hDiff1 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))) :=
    primrec_selectFn hb2 hemptyInter hemptyDiff
  have hsplitIdx : Nat.Primrec (fun w => selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (hSplitY.posIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))
      (hSplitY.negIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))) :=
    primrec_selectFn hb2 hposIdx hnegIdx
  have hnewJunk : Nat.Primrec (fun w => selectFn (_root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) 1 (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₁ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P₁ hDiff1 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))))) :=
    primrec_selectFn hjunk (Nat.Primrec.const 1) hdirectEmpty
  have hidx0' : Nat.Primrec (fun w => selectFn (selectFn (_root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) 1 (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₁ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P₁ hDiff1 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))))) 0
      (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w) (hSplitY.posIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))
        (hSplitY.negIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.stateIdx0 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hsplitIdx
  have hidx1' : Nat.Primrec (fun w => selectFn (selectFn (_root_.DomainTheory.NeighbourhoodSystems.stateJunk (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) 1 (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w)
      (_root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P₁ (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))
      (_root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P₁ hDiff1 (Nat.pair (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))))) 0
      (selectFn (_root_.DomainTheory.NeighbourhoodSystems.xwB1 w) (P₁.inter (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w))
        (hDiff1.diffIdx (_root_.DomainTheory.NeighbourhoodSystems.stateIdx1 (_root_.DomainTheory.NeighbourhoodSystems.xwS w)) (_root_.DomainTheory.NeighbourhoodSystems.xwN w)))) :=
    primrec_selectFn hnewJunk (Nat.Primrec.const 0) hdirectIdx
  exact (hidx0'.pair (hidx1'.pair hnewJunk)).of_eq fun w => by
    unfold _root_.DomainTheory.NeighbourhoodSystems.ySubStep packState2
    simp only []

end YSubStep

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

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

end AtomPairCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem atomPairCodeState :
    Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY) :=
  (Nat.Primrec.prec (primrec.atomPairBase P₀ P₁)
    (primrec.atomPairStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY)).of_eq fun _ => rfl

end AtomPairCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem atomPairIdx0 : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
  (primrec.stateIdx0.comp (primrec.stateInnerC.comp
    ((primrec.atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp
      (Nat.Primrec.right.pair Nat.Primrec.left)))).of_eq fun _ => rfl

end AtomPairCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem atomPairIdx1 : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
  (primrec.stateIdx1.comp (primrec.stateInnerC.comp
    ((primrec.atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp
      (Nat.Primrec.right.pair Nat.Primrec.left)))).of_eq fun _ => rfl

end AtomPairCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section AtomPairCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)

theorem atomPairJunk : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
  (primrec.stateJunk.comp (primrec.stateInnerC.comp
    ((primrec.atomPairCodeState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp
      (Nat.Primrec.right.pair Nat.Primrec.left)))).of_eq fun _ => rfl

end AtomPairCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section _root_.DomainTheory.NeighbourhoodSystems.XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

theorem xPseqAtomState : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hidx0 : Nat.Primrec (fun t : ℕ =>
      _root_.DomainTheory.NeighbourhoodSystems.atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
    primrec.atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
  have hidx1 : Nat.Primrec (fun t : ℕ =>
      _root_.DomainTheory.NeighbourhoodSystems.atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
    primrec.atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
  have hjunk : Nat.Primrec (fun t : ℕ =>
      _root_.DomainTheory.NeighbourhoodSystems.atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2) :=
    primrec.atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
  have hpacked : Nat.Primrec (fun t : ℕ => packState2
      (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2)
      (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2)
      (_root_.DomainTheory.NeighbourhoodSystems.atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2)) :=
    (hidx0.pair (hidx1.pair hjunk)).of_eq fun _ => rfl
  have hinner : Nat.Primrec (fun t : ℕ => Nat.pair 1 (packState2
      (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2)
      (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2)
      (_root_.DomainTheory.NeighbourhoodSystems.atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1 t.unpair.2))) :=
    (Nat.Primrec.const 1).pair hpacked
  exact ((primrec.xSubStep P₀ P₁ hDiff0 splitX hSplitX).comp (hn.pair hinner)).of_eq fun _ => rfl

end _root_.DomainTheory.NeighbourhoodSystems.XPseqCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section _root_.DomainTheory.NeighbourhoodSystems.XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

theorem xPseqAtomIdx : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2) :=
  (primrec.stateIdx1.comp (primrec.xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY)).of_eq fun _ => rfl

end _root_.DomainTheory.NeighbourhoodSystems.XPseqCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section _root_.DomainTheory.NeighbourhoodSystems.XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

theorem xPseqAtomJunk : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2) :=
  (primrec.stateJunk.comp (primrec.xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY)).of_eq fun _ => rfl

end _root_.DomainTheory.NeighbourhoodSystems.XPseqCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section _root_.DomainTheory.NeighbourhoodSystems.XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

theorem XFoldStep :
    Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.XFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) := by
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hni : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.1 w.unpair.2.unpair.1) := hn.pair hi
  have hjunk : Nat.Primrec (fun w : ℕ =>
      _root_.DomainTheory.NeighbourhoodSystems.xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1
        w.unpair.2.unpair.1) :=
    ((primrec.xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hni).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hidx : Nat.Primrec (fun w : ℕ =>
      _root_.DomainTheory.NeighbourhoodSystems.xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1
        w.unpair.2.unpair.1) :=
    ((primrec.xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hni).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hfound : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp hacc
  have hval : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp hacc
  have hunion : Nat.Primrec (fun w : ℕ => hUnion1.unionIdx w.unpair.2.unpair.2.unpair.2
      (_root_.DomainTheory.NeighbourhoodSystems.xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1
        w.unpair.2.unpair.1)) :=
    (hUnion1.unionIdx_primrec.comp (hval.pair hidx)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hinner : Nat.Primrec (fun w : ℕ => selectFn w.unpair.2.unpair.2.unpair.1
      (Nat.pair 1 (hUnion1.unionIdx w.unpair.2.unpair.2.unpair.2
        (_root_.DomainTheory.NeighbourhoodSystems.xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1
          w.unpair.2.unpair.1)))
      (Nat.pair 1 (_root_.DomainTheory.NeighbourhoodSystems.xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1
        w.unpair.2.unpair.1))) :=
    primrec_selectFn hfound ((Nat.Primrec.const 1).pair hunion) ((Nat.Primrec.const 1).pair hidx)
  exact (primrec_selectFn hjunk hacc hinner).of_eq fun w => by unfold _root_.DomainTheory.NeighbourhoodSystems.XFoldStep; simp only []

end _root_.DomainTheory.NeighbourhoodSystems.XPseqCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section _root_.DomainTheory.NeighbourhoodSystems.XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

theorem XFold : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
      t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const (Nat.pair 0 0))
    (primrec.XFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1)).of_eq
    fun _ => rfl

end _root_.DomainTheory.NeighbourhoodSystems.XPseqCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section _root_.DomainTheory.NeighbourhoodSystems.XPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₁pos : D₁.IsPositive) (hD₁diff : D₁.DiffClosed) (hD₁nomin : D₁.NoMinimal)
  (hUnion1 : IsComputableUnion P₁)

theorem XPseqCode : Nat.Primrec
    (_root_.DomainTheory.NeighbourhoodSystems.XPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1) := by
  have h4n : Nat.Primrec (fun n : ℕ => 4 ^ n) := primrec_pow₂ (Nat.Primrec.const 4) Nat.Primrec.id
  refine (Nat.Primrec.right.comp
    ((primrec.XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1).comp
      (Nat.Primrec.id.pair h4n))).of_eq fun n => ?_
  show (_root_.DomainTheory.NeighbourhoodSystems.XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
    (Nat.pair n (4 ^ n)).unpair.1 (Nat.pair n (4 ^ n)).unpair.2).unpair.2 = _root_.DomainTheory.NeighbourhoodSystems.XPseqCode P₀ P₁ hDiff0
      hDiff1 splitX hSplitX splitY hSplitY hUnion1 n
  rw [unpair_pair_fst, unpair_pair_snd]; rfl

end _root_.DomainTheory.NeighbourhoodSystems.XPseqCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

theorem yPseqAtomState : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hi : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hbx : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hni : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2.unpair.1) := hn.pair hi
  have hidx0 : Nat.Primrec (fun t : ℕ =>
      _root_.DomainTheory.NeighbourhoodSystems.atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1) :=
    ((primrec.atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hni).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hidx1 : Nat.Primrec (fun t : ℕ =>
      _root_.DomainTheory.NeighbourhoodSystems.atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1) :=
    ((primrec.atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hni).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hjunk : Nat.Primrec (fun t : ℕ =>
      _root_.DomainTheory.NeighbourhoodSystems.atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1) :=
    ((primrec.atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hni).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hpacked : Nat.Primrec (fun t : ℕ => packState2
      (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1)
      (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1)
      (_root_.DomainTheory.NeighbourhoodSystems.atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1)) :=
    (hidx0.pair (hidx1.pair hjunk)).of_eq fun _ => rfl
  have hxinner : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 (packState2
      (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1)
      (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1)
      (_root_.DomainTheory.NeighbourhoodSystems.atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
        t.unpair.2.unpair.1))) :=
    hbx.pair hpacked
  have hxarg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (Nat.pair t.unpair.2.unpair.2
      (packState2 (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
          t.unpair.2.unpair.1)
        (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
          t.unpair.2.unpair.1)
        (_root_.DomainTheory.NeighbourhoodSystems.atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
          t.unpair.2.unpair.1)))) :=
    hn.pair hxinner
  have hxstep : Nat.Primrec (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair
      t.unpair.1 (Nat.pair t.unpair.2.unpair.2 (packState2
        (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
          t.unpair.2.unpair.1)
        (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
          t.unpair.2.unpair.1)
        (_root_.DomainTheory.NeighbourhoodSystems.atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
          t.unpair.2.unpair.1))))) :=
    (primrec.xSubStep P₀ P₁ hDiff0 splitX hSplitX).comp hxarg
  have hystep_arg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (Nat.pair 1
      (_root_.DomainTheory.NeighbourhoodSystems.xSubStep P₀ P₁ hDiff0 splitX hSplitX (Nat.pair t.unpair.1 (Nat.pair t.unpair.2.unpair.2
        (packState2 (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx0 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
            t.unpair.2.unpair.1)
          (_root_.DomainTheory.NeighbourhoodSystems.atomPairIdx1 P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
            t.unpair.2.unpair.1)
          (_root_.DomainTheory.NeighbourhoodSystems.atomPairJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY t.unpair.1
            t.unpair.2.unpair.1))))))) :=
    hn.pair ((Nat.Primrec.const 1).pair hxstep)
  exact ((primrec.ySubStep P₀ P₁ hDiff1 splitY hSplitY).comp hystep_arg).of_eq fun _ => rfl

end _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

theorem yPseqAtomIdx : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) :=
  (primrec.stateIdx0.comp (primrec.yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY)).of_eq fun _ => rfl

end _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

theorem yPseqAtomJunk : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) :=
  (primrec.stateJunk.comp (primrec.yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY)).of_eq fun _ => rfl

end _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

theorem YFoldStep :
    Nat.Primrec (_root_.DomainTheory.NeighbourhoodSystems.YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) := by
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have hbx : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hnibx : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.1.unpair.1
      (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2)) := hn.pair (hi.pair hbx)
  have hjunk : Nat.Primrec (fun w : ℕ =>
      _root_.DomainTheory.NeighbourhoodSystems.yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1.unpair.1
        w.unpair.2.unpair.1 w.unpair.1.unpair.2) :=
    ((primrec.yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hnibx).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hidx : Nat.Primrec (fun w : ℕ =>
      _root_.DomainTheory.NeighbourhoodSystems.yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1.unpair.1
        w.unpair.2.unpair.1 w.unpair.1.unpair.2) :=
    ((primrec.yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY).comp hnibx).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hfound : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp hacc
  have hval : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp hacc
  have hunion : Nat.Primrec (fun w : ℕ => hUnion0.unionIdx w.unpair.2.unpair.2.unpair.2
      (_root_.DomainTheory.NeighbourhoodSystems.yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1.unpair.1
        w.unpair.2.unpair.1 w.unpair.1.unpair.2)) :=
    (hUnion0.unionIdx_primrec.comp (hval.pair hidx)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hinner : Nat.Primrec (fun w : ℕ => selectFn w.unpair.2.unpair.2.unpair.1
      (Nat.pair 1 (hUnion0.unionIdx w.unpair.2.unpair.2.unpair.2
        (_root_.DomainTheory.NeighbourhoodSystems.yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY w.unpair.1.unpair.1
          w.unpair.2.unpair.1 w.unpair.1.unpair.2)))
      (Nat.pair 1 (_root_.DomainTheory.NeighbourhoodSystems.yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
        w.unpair.1.unpair.1 w.unpair.2.unpair.1 w.unpair.1.unpair.2))) :=
    primrec_selectFn hfound ((Nat.Primrec.const 1).pair hunion) ((Nat.Primrec.const 1).pair hidx)
  exact (primrec_selectFn hjunk hacc hinner).of_eq fun w => by unfold _root_.DomainTheory.NeighbourhoodSystems.YFoldStep; simp only []

end _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

theorem YFoldInnerPair : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.YFoldInnerPair P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const (Nat.pair 0 0))
    (primrec.YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0)).of_eq
    fun _ => rfl

end _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

theorem YFoldInner : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2) := by
  have h1 : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1.unpair.1 t.unpair.1.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.left)
  have h2 : Nat.Primrec (fun t : ℕ => Nat.pair
      (Nat.pair t.unpair.1.unpair.1 t.unpair.1.unpair.2) t.unpair.2) :=
    h1.pair Nat.Primrec.right
  exact ((primrec.YFoldInnerPair P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0).comp
    h2).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
      exact (YFoldInner.eq_pair P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
        t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2).symm

end _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

end primrec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace primrec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

variable {α β : Type*} {D₀ : NeighborhoodSystem α} {D₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation D₀) (P₁ : ComputablePresentation D₁)
  (hDiff0 : IsComputableDiff P₀) (hDiff1 : IsComputableDiff P₁)
  (splitX : Set α → Set β → Set α → Set β × Set β) (hSplitX : IsComputableSplit P₀ P₁ splitX)
  (splitY : Set β → Set α → Set β → Set α × Set α) (hSplitY : IsComputableSplit P₁ P₀ splitY)
  (hD₀pos : D₀.IsPositive) (hD₀diff : D₀.DiffClosed) (hD₀nomin : D₀.NoMinimal)
  (hUnion0 : IsComputableUnion P₀)

theorem YPseqCode : Nat.Primrec
    (_root_.DomainTheory.NeighbourhoodSystems.YPseqCode P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0) := by
  have h4n : Nat.Primrec (fun n : ℕ => 4 ^ n) := primrec_pow₂ (Nat.Primrec.const 4) Nat.Primrec.id
  have hr0 : Nat.Primrec (fun n : ℕ =>
      _root_.DomainTheory.NeighbourhoodSystems.YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n)) := by
    have harg : Nat.Primrec (fun n : ℕ => Nat.pair (Nat.pair n 0) (4 ^ n)) :=
      (Nat.Primrec.id.pair (Nat.Primrec.const 0)).pair h4n
    exact ((primrec.YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0).comp
      harg).of_eq fun n => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hr1 : Nat.Primrec (fun n : ℕ =>
      _root_.DomainTheory.NeighbourhoodSystems.YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n)) := by
    have harg : Nat.Primrec (fun n : ℕ => Nat.pair (Nat.pair n 1) (4 ^ n)) :=
      (Nat.Primrec.id.pair (Nat.Primrec.const 1)).pair h4n
    exact ((primrec.YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0).comp
      harg).of_eq fun n => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hcomb : Nat.Primrec (fun n : ℕ => _root_.DomainTheory.NeighbourhoodSystems.combineFound2 hUnion0
      (_root_.DomainTheory.NeighbourhoodSystems.YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n))
      (_root_.DomainTheory.NeighbourhoodSystems.YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n))) :=
    ((primrec.combineFound2 hUnion0).comp (hr0.pair hr1)).of_eq
      fun n => by simp only [unpair_pair_fst, unpair_pair_snd]
  exact (Nat.Primrec.right.comp hcomb).of_eq fun _ => rfl

end _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

end primrec
end DomainTheory.NeighbourhoodSystems
