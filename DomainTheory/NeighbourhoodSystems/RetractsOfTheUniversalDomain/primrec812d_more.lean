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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812d_early_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.combinedCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec812d

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

namespace primrec
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

theorem xPseqAtomIdx : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.xPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2) :=
  (primrec.stateIdx1.comp (primrec.xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY)).of_eq fun _ => rfl

theorem xPseqAtomJunk : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.xPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2) :=
  (primrec.stateJunk.comp (primrec.xPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY)).of_eq fun _ => rfl

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

theorem XFold : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.XFold P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1
      t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const (Nat.pair 0 0))
    (primrec.XFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion1)).of_eq
    fun _ => rfl

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

theorem yPseqAtomIdx : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.yPseqAtomIdx P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) :=
  (primrec.stateIdx0.comp (primrec.yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY)).of_eq fun _ => rfl

theorem yPseqAtomJunk : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.yPseqAtomJunk P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) :=
  (primrec.stateJunk.comp (primrec.yPseqAtomState P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY
    hSplitY)).of_eq fun _ => rfl

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

theorem YFoldInnerPair : Nat.Primrec
    (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.YFoldInnerPair P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0
      t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const (Nat.pair 0 0))
    (primrec.YFoldStep P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0)).of_eq
    fun _ => rfl

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
  have hcomb : Nat.Primrec (fun n : ℕ => _root_.DomainTheory.NeighbourhoodSystems.IsComputableUnion.combineFound2 hUnion0
      (_root_.DomainTheory.NeighbourhoodSystems.YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 0 (4 ^ n))
      (_root_.DomainTheory.NeighbourhoodSystems.YFoldInner P₀ P₁ hDiff0 hDiff1 splitX hSplitX splitY hSplitY hUnion0 n 1 (4 ^ n))) :=
    ((primrec.IsComputableUnion.combineFound2 hUnion0).comp (hr0.pair hr1)).of_eq
      fun n => by simp only [unpair_pair_fst, unpair_pair_snd]
  exact (Nat.Primrec.right.comp hcomb).of_eq fun _ => rfl

end _root_.DomainTheory.NeighbourhoodSystems.YPseqCode

end primrec

end DomainTheory.NeighbourhoodSystems
