module

public import DomainTheory.DataTypesAsLattices.Retracts.expR
public import DomainTheory.DataTypesAsLattices.Functionality.CombC
public import DomainTheory.DataTypesAsLattices.Retracts.updateEnv
public import DomainTheory.DataTypesAsLattices.Retracts.envR
import DomainTheory.DataTypesAsLattices.Retracts.eq_4_44
import DomainTheory.DataTypesAsLattices.Retracts.typed_more
import DomainTheory.DataTypesAsLattices.Retracts.arrowR_more
import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_4
import DomainTheory.DataTypesAsLattices.Functionality.PlotkinHelpers
import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
import DomainTheory.DataTypesAsLattices.Enumeration.ContinuityHelpers
import DomainTheory.DataTypesAsLattices.Enumeration.PairSeq
import DomainTheory.DataTypesAsLattices.Lambda.succSet_more
import DomainTheory.DataTypesAsLattices.Lambda.predSet_more
import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
import DomainTheory.DataTypesAsLattices.Graph.beta
import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

inductive LambTerm where
  | var : ℕ → LambTerm
  | zero : LambTerm
  | succ : LambTerm → LambTerm
  | pred : LambTerm → LambTerm
  | condq : LambTerm → LambTerm → LambTerm → LambTerm → LambTerm
  | app : LambTerm → LambTerm → LambTerm
  | lam : ℕ → LambTerm → LambTerm

def encodeExp : LambTerm → Pomega
  | .var n => tagInj 0 (ofNat n)
  | .zero => tagInj 1 botElem
  | .succ τ => tagInj 2 (encodeExp τ)
  | .pred τ => tagInj 3 (encodeExp τ)
  | .condq θ τ σ ρ =>
      tagInj 4 (seq4 (encodeExp θ) (encodeExp τ) (encodeExp σ) (encodeExp ρ))
  | .app τ σ => tagInj 5 (pairSeq (encodeExp τ) (encodeExp σ))
  | .lam n τ => tagInj 6 (pairSeq (ofNat n) (encodeExp τ))

namespace encodeExp

theorem typed : ∀ τ : LambTerm, typed (encodeExp τ) expR := by
  intro τ
  induction τ with
  | var n =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    exact plus7.typed_inl0 (typed.ofNat_intR n)
  | zero =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    exact plus7.typed_inl1 typed.bot_botElem
  | succ τ ih =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    exact plus7.typed_inl2 ih
  | pred τ ih =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    exact plus7.typed_inl3 ih
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    refine plus7.typed_inl4 ?_
    rw [DomainTheory.DataTypesAsLattices.typed, tensor4.app, seq4.zero, seq4.one, seq4.two,
      seq4.three, ← ihθ, ← ihτ, ← ihσ, ← ihρ]
  | app τ σ ihτ ihσ =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    refine plus7.typed_inl5 ?_
    exact (typed.pairSeq_tensorR expR expR _ _).mpr ⟨ihτ, ihσ⟩
  | lam n τ ih =>
    rw [encodeExp, DomainTheory.DataTypesAsLattices.eq_4_44]
    refine plus7.typed_inl6 ?_
    exact (typed.pairSeq_tensorR intR expR _ _).mpr ⟨typed.ofNat_intR n, ih⟩

end encodeExp

def expTag (e : Pomega) : Pomega := funOf e (ofNat 0)

def expPayload (e : Pomega) : Pomega := funOf e (ofNat 1)


def hApply (H e t : Pomega) : Pomega := funOf (funOf H e) t

namespace hApply

theorem isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hApply H e t) :=
  theorem_1_3 (f := fun u => funOf u t) (g := fun H => funOf H e)
    (funOf.isScottContinuous_left t) (funOf.isScottContinuous_left e)

theorem isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hApply H e t) :=
  theorem_1_3 (f := fun u => funOf u t) (g := funOf H)
    (funOf.isScottContinuous_left t) (funOf.isScottContinuous H)

theorem payload_isScottContinuous_e (H t : Pomega) (i : ℕ) :
    IsScottContinuous (fun e =>
      hApply H (funOf (expPayload e) (ofNat i)) t) :=
  theorem_1_3 (f := fun e => hApply H e t)
    (g := fun e => funOf (expPayload e) (ofNat i))
    (isScottContinuous_e H t)
    (theorem_1_3 (f := fun u => funOf u (ofNat i)) (g := expPayload)
      (funOf.isScottContinuous_left (ofNat i))
      (funOf.isScottContinuous_left (ofNat 1)))

end hApply


def hVar (e t : Pomega) : Pomega := funOf t (expPayload e)

namespace hVar

theorem isScottContinuous_t (e : Pomega) :
    IsScottContinuous (fun t => hVar e t) :=
  funOf.isScottContinuous_left (expPayload e)

theorem isScottContinuous_e (t : Pomega) :
    IsScottContinuous (fun e => hVar e t) :=
  theorem_1_3 (f := funOf t) (g := expPayload)
    (funOf.isScottContinuous t) (funOf.isScottContinuous_left (ofNat 1))

end hVar


def hZero : Pomega := funOf inleftC (ofNat 0)


def hApp (H e t : Pomega) : Pomega :=
  condSet (funOf whichC (hApply H (funOf (expPayload e) (ofNat 0)) t)) botElem
    (funOf (funOf outC (hApply H (funOf (expPayload e) (ofNat 0)) t))
      (hApply H (funOf (expPayload e) (ofNat 1)) t))

namespace hApp

theorem isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hApp H e t) :=
  ContinuityHelpers.nary
    (fun y z => condSet.isScottContinuous_left y z)
    (fun x z => condSet.isScottContinuous_mid x z)
    (fun x y => condSet.isScottContinuous_right x y)
    (theorem_1_3 (funOf.isScottContinuous whichC)
      (hApply.isScottContinuous_H _ t))
    (const_isScottContinuous botElem)
    (ContinuityHelpers.tuple
      (fun y => funOf.isScottContinuous_left y)
      (fun u => funOf.isScottContinuous u)
      (theorem_1_3 (funOf.isScottContinuous outC)
        (hApply.isScottContinuous_H _ t))
      (hApply.isScottContinuous_H _ t))

theorem isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hApp H e t) :=
  ContinuityHelpers.nary
    (fun y z => condSet.isScottContinuous_left y z)
    (fun x z => condSet.isScottContinuous_mid x z)
    (fun x y => condSet.isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC)
      (g := fun t => hApply H (funOf (expPayload e) (ofNat 0)) t)
      (funOf.isScottContinuous whichC)
      (funOf.isScottContinuous (funOf H (funOf (expPayload e) (ofNat 0)))))
    (const_isScottContinuous botElem)
    (ContinuityHelpers.tuple
      (fun y => funOf.isScottContinuous_left y)
      (fun u => funOf.isScottContinuous u)
      (theorem_1_3 (f := funOf outC)
        (g := fun t => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf.isScottContinuous outC)
        (funOf.isScottContinuous (funOf H (funOf (expPayload e) (ofNat 0)))))
      (funOf.isScottContinuous (funOf H (funOf (expPayload e) (ofNat 1)))))

theorem isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hApp H e t) :=
  ContinuityHelpers.nary
    (fun y z => condSet.isScottContinuous_left y z)
    (fun x z => condSet.isScottContinuous_mid x z)
    (fun x y => condSet.isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC)
      (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
      (funOf.isScottContinuous whichC)
      (hApply.payload_isScottContinuous_e H t 0))
    (const_isScottContinuous botElem)
    (ContinuityHelpers.tuple
      (fun y => funOf.isScottContinuous_left y)
      (fun u => funOf.isScottContinuous u)
      (theorem_1_3 (f := funOf outC)
        (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf.isScottContinuous outC)
        (hApply.payload_isScottContinuous_e H t 0))
      (hApply.payload_isScottContinuous_e H t 1))

end hApp


def hSucc (H e t : Pomega) : Pomega :=
  condSet (funOf whichC (hApply H (expPayload e) t))
    (funOf inleftC (succSet (funOf outC (hApply H (expPayload e) t))))
    botElem

namespace hSucc

theorem isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hSucc H e t) :=
  ContinuityHelpers.nary
    (fun y z => condSet.isScottContinuous_left y z)
    (fun x z => condSet.isScottContinuous_mid x z)
    (fun x y => condSet.isScottContinuous_right x y)
    (theorem_1_3 (funOf.isScottContinuous whichC) (hApply.isScottContinuous_H _ t))
    (theorem_1_3 (funOf.isScottContinuous inleftC)
      (theorem_1_3 succSet.isScottContinuous
        (theorem_1_3 (funOf.isScottContinuous outC)
          (hApply.isScottContinuous_H _ t))))
    (const_isScottContinuous botElem)

theorem isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hSucc H e t) :=
  ContinuityHelpers.nary
    (fun y z => condSet.isScottContinuous_left y z)
    (fun x z => condSet.isScottContinuous_mid x z)
    (fun x y => condSet.isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC) (g := fun t => hApply H (expPayload e) t)
      (funOf.isScottContinuous whichC)
      (funOf.isScottContinuous (funOf H (expPayload e))))
    (theorem_1_3 (f := funOf inleftC)
      (g := fun t => succSet (funOf outC (hApply H (expPayload e) t)))
      (funOf.isScottContinuous inleftC)
      (theorem_1_3 (f := succSet)
        (g := fun t => funOf outC (hApply H (expPayload e) t))
        succSet.isScottContinuous
        (theorem_1_3 (f := funOf outC) (g := fun t => hApply H (expPayload e) t)
          (funOf.isScottContinuous outC)
          (funOf.isScottContinuous (funOf H (expPayload e))))))
    (const_isScottContinuous botElem)

theorem isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hSucc H e t) :=
  let hrec :=
    theorem_1_3 (f := fun e => hApply H e t) (g := expPayload)
      (hApply.isScottContinuous_e H t)
      (funOf.isScottContinuous_left (ofNat 1))
  ContinuityHelpers.nary
    (fun y z => condSet.isScottContinuous_left y z)
    (fun x z => condSet.isScottContinuous_mid x z)
    (fun x y => condSet.isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC) (g := fun e => hApply H (expPayload e) t)
      (funOf.isScottContinuous whichC) hrec)
    (theorem_1_3 (f := funOf inleftC)
      (g := fun e => succSet (funOf outC (hApply H (expPayload e) t)))
      (funOf.isScottContinuous inleftC)
      (theorem_1_3 (f := succSet)
        (g := fun e => funOf outC (hApply H (expPayload e) t))
        succSet.isScottContinuous
        (theorem_1_3 (f := funOf outC) (g := fun e => hApply H (expPayload e) t)
          (funOf.isScottContinuous outC) hrec)))
    (const_isScottContinuous botElem)

end hSucc


def hPred (H e t : Pomega) : Pomega :=
  condSet (funOf whichC (hApply H (expPayload e) t))
    (funOf inleftC (predSet (funOf outC (hApply H (expPayload e) t))))
    botElem

namespace hPred

theorem isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hPred H e t) :=
  ContinuityHelpers.nary
    (fun y z => condSet.isScottContinuous_left y z)
    (fun x z => condSet.isScottContinuous_mid x z)
    (fun x y => condSet.isScottContinuous_right x y)
    (theorem_1_3 (funOf.isScottContinuous whichC) (hApply.isScottContinuous_H _ t))
    (theorem_1_3 (funOf.isScottContinuous inleftC)
      (theorem_1_3 predSet.isScottContinuous
        (theorem_1_3 (funOf.isScottContinuous outC)
          (hApply.isScottContinuous_H _ t))))
    (const_isScottContinuous botElem)

theorem isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hPred H e t) :=
  ContinuityHelpers.nary
    (fun y z => condSet.isScottContinuous_left y z)
    (fun x z => condSet.isScottContinuous_mid x z)
    (fun x y => condSet.isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC) (g := fun t => hApply H (expPayload e) t)
      (funOf.isScottContinuous whichC)
      (funOf.isScottContinuous (funOf H (expPayload e))))
    (theorem_1_3 (f := funOf inleftC)
      (g := fun t => predSet (funOf outC (hApply H (expPayload e) t)))
      (funOf.isScottContinuous inleftC)
      (theorem_1_3 (f := predSet)
        (g := fun t => funOf outC (hApply H (expPayload e) t))
        predSet.isScottContinuous
        (theorem_1_3 (f := funOf outC) (g := fun t => hApply H (expPayload e) t)
          (funOf.isScottContinuous outC)
          (funOf.isScottContinuous (funOf H (expPayload e))))))
    (const_isScottContinuous botElem)

theorem isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hPred H e t) :=
  let hrec :=
    theorem_1_3 (f := fun e => hApply H e t) (g := expPayload)
      (hApply.isScottContinuous_e H t)
      (funOf.isScottContinuous_left (ofNat 1))
  ContinuityHelpers.nary
    (fun y z => condSet.isScottContinuous_left y z)
    (fun x z => condSet.isScottContinuous_mid x z)
    (fun x y => condSet.isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC) (g := fun e => hApply H (expPayload e) t)
      (funOf.isScottContinuous whichC) hrec)
    (theorem_1_3 (f := funOf inleftC)
      (g := fun e => predSet (funOf outC (hApply H (expPayload e) t)))
      (funOf.isScottContinuous inleftC)
      (theorem_1_3 (f := predSet)
        (g := fun e => funOf outC (hApply H (expPayload e) t))
        predSet.isScottContinuous
        (theorem_1_3 (f := funOf outC) (g := fun e => hApply H (expPayload e) t)
          (funOf.isScottContinuous outC) hrec)))
    (const_isScottContinuous botElem)

end hPred


def hCond (H e t : Pomega) : Pomega :=
  funOf lambR
    (condSet (funOf whichC (hApply H (funOf (expPayload e) (ofNat 0)) t))
      (condSet (funOf outC (hApply H (funOf (expPayload e) (ofNat 0)) t))
        (hApply H (funOf (expPayload e) (ofNat 1)) t)
        (hApply H (funOf (expPayload e) (ofNat 2)) t))
      (hApply H (funOf (expPayload e) (ofNat 3)) t))

namespace hCond

theorem isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hCond H e t) :=
  theorem_1_3 (funOf.isScottContinuous lambR)
    (ContinuityHelpers.nary
      (fun y z => condSet.isScottContinuous_left y z)
      (fun x z => condSet.isScottContinuous_mid x z)
      (fun x y => condSet.isScottContinuous_right x y)
      (theorem_1_3 (funOf.isScottContinuous whichC)
        (hApply.isScottContinuous_H _ t))
      (ContinuityHelpers.nary
        (fun y z => condSet.isScottContinuous_left y z)
        (fun x z => condSet.isScottContinuous_mid x z)
        (fun x y => condSet.isScottContinuous_right x y)
        (theorem_1_3 (funOf.isScottContinuous outC)
          (hApply.isScottContinuous_H _ t))
        (hApply.isScottContinuous_H _ t)
        (hApply.isScottContinuous_H _ t))
      (hApply.isScottContinuous_H _ t))

theorem isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hCond H e t) :=
  theorem_1_3 (f := funOf lambR)
    (g := fun t =>
      condSet (funOf whichC (hApply H (funOf (expPayload e) (ofNat 0)) t))
        (condSet (funOf outC (hApply H (funOf (expPayload e) (ofNat 0)) t))
          (hApply H (funOf (expPayload e) (ofNat 1)) t)
          (hApply H (funOf (expPayload e) (ofNat 2)) t))
        (hApply H (funOf (expPayload e) (ofNat 3)) t))
    (funOf.isScottContinuous lambR)
    (ContinuityHelpers.nary
      (fun y z => condSet.isScottContinuous_left y z)
      (fun x z => condSet.isScottContinuous_mid x z)
      (fun x y => condSet.isScottContinuous_right x y)
      (theorem_1_3 (f := funOf whichC)
        (g := fun t => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf.isScottContinuous whichC)
        (funOf.isScottContinuous (funOf H (funOf (expPayload e) (ofNat 0)))))
      (ContinuityHelpers.nary
        (fun y z => condSet.isScottContinuous_left y z)
        (fun x z => condSet.isScottContinuous_mid x z)
        (fun x y => condSet.isScottContinuous_right x y)
        (theorem_1_3 (f := funOf outC)
          (g := fun t => hApply H (funOf (expPayload e) (ofNat 0)) t)
          (funOf.isScottContinuous outC)
          (funOf.isScottContinuous (funOf H (funOf (expPayload e) (ofNat 0)))))
        (funOf.isScottContinuous (funOf H (funOf (expPayload e) (ofNat 1))))
        (funOf.isScottContinuous (funOf H (funOf (expPayload e) (ofNat 2)))))
      (funOf.isScottContinuous (funOf H (funOf (expPayload e) (ofNat 3)))))

theorem isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hCond H e t) :=
  theorem_1_3 (f := funOf lambR)
    (g := fun e =>
      condSet (funOf whichC (hApply H (funOf (expPayload e) (ofNat 0)) t))
        (condSet (funOf outC (hApply H (funOf (expPayload e) (ofNat 0)) t))
          (hApply H (funOf (expPayload e) (ofNat 1)) t)
          (hApply H (funOf (expPayload e) (ofNat 2)) t))
        (hApply H (funOf (expPayload e) (ofNat 3)) t))
    (funOf.isScottContinuous lambR)
    (ContinuityHelpers.nary
      (fun y z => condSet.isScottContinuous_left y z)
      (fun x z => condSet.isScottContinuous_mid x z)
      (fun x y => condSet.isScottContinuous_right x y)
      (theorem_1_3 (f := funOf whichC)
        (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf.isScottContinuous whichC)
        (hApply.payload_isScottContinuous_e H t 0))
      (ContinuityHelpers.nary
        (fun y z => condSet.isScottContinuous_left y z)
        (fun x z => condSet.isScottContinuous_mid x z)
        (fun x y => condSet.isScottContinuous_right x y)
        (theorem_1_3 (f := funOf outC)
          (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
          (funOf.isScottContinuous outC)
          (hApply.payload_isScottContinuous_e H t 0))
        (hApply.payload_isScottContinuous_e H t 1)
        (hApply.payload_isScottContinuous_e H t 2))
      (hApply.payload_isScottContinuous_e H t 3))

end hCond


def hLam (H e t : Pomega) : Pomega :=
  funOf inrightC
    (graph (fun x =>
      hApply H (funOf (expPayload e) (ofNat 1))
        (updateEnv.union t x (funOf (expPayload e) (ofNat 0)))))

namespace hLam

theorem isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hLam H e t) :=
  theorem_1_3 (funOf.isScottContinuous inrightC)
    (graph_const_isScottContinuous
      (fun H x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnv.union t x (funOf (expPayload e) (ofNat 0))))
      (fun _ => hApply.isScottContinuous_H _ _))

theorem isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => hLam H e t) :=
  theorem_1_3 (f := funOf inrightC)
    (g := fun t =>
      graph (fun x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnv.union t x (funOf (expPayload e) (ofNat 0)))))
    (funOf.isScottContinuous inrightC)
    (graph_const_isScottContinuous
      (fun t x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnv.union t x (funOf (expPayload e) (ofNat 0))))
      (fun x =>
        theorem_1_3
          (f := funOf (funOf H (funOf (expPayload e) (ofNat 1))))
          (g := fun t => updateEnv.union t x (funOf (expPayload e) (ofNat 0)))
          (funOf.isScottContinuous (funOf H (funOf (expPayload e) (ofNat 1))))
          (updateEnv.union_isScottContinuous_t x
            (funOf (expPayload e) (ofNat 0)))))

theorem isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hLam H e t) :=
  theorem_1_3 (f := funOf inrightC)
    (g := fun e =>
      graph (fun x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnv.union t x (funOf (expPayload e) (ofNat 0)))))
    (funOf.isScottContinuous inrightC)
    (graph_const_isScottContinuous
      (fun e x =>
        hApply H (funOf (expPayload e) (ofNat 1))
          (updateEnv.union t x (funOf (expPayload e) (ofNat 0))))
      (fun x =>
        ContinuityHelpers.tuple
          (fun y =>
            theorem_1_3 (f := fun u => funOf u y) (g := funOf H)
              (funOf.isScottContinuous_left y) (funOf.isScottContinuous H))
          (fun u => funOf.isScottContinuous (funOf H u))
          (theorem_1_3 (f := fun u => funOf u (ofNat 1)) (g := expPayload)
            (funOf.isScottContinuous_left (ofNat 1))
            (funOf.isScottContinuous_left (ofNat 1)))
          (theorem_1_3 (f := updateEnv.union t x)
            (g := fun e => funOf (expPayload e) (ofNat 0))
            (updateEnv.isScottContinuous_idx t x)
            (theorem_1_3 (f := fun u => funOf u (ofNat 0)) (g := expPayload)
              (funOf.isScottContinuous_left (ofNat 0))
              (funOf.isScottContinuous_left (ofNat 1))))))

end hLam


def Hstep (H e t : Pomega) : Pomega :=
  dcondSet (expTag e) (hVar e t)
    (dcondSet (predSet (expTag e)) hZero
      (dcondSet (predSet (predSet (expTag e))) (hSucc H e t)
        (dcondSet (predSet^[3] (expTag e)) (hPred H e t)
          (dcondSet (predSet^[4] (expTag e)) (hCond H e t)
            (dcondSet (predSet^[5] (expTag e)) (hApp H e t)
              (dcondSet (predSet^[6] (expTag e)) (hLam H e t)
                topElem))))))

namespace Hstep

theorem tag0 (H x t : Pomega) :
    Hstep H (tagInj 0 x) t = funOf t x := by
  simp only [Hstep, expTag, expPayload, hVar, tagInj.zero, tagInj.one,
    dcondSet.ofNat_zero]

theorem tag1 (H x t : Pomega) :
    Hstep H (tagInj 1 x) t = hZero := by
  simp only [Hstep, expTag, tagInj.zero, predSet.ofNat_succ,
    dcondSet.ofNat_one, dcondSet.ofNat_zero]

theorem tag2 (H x t : Pomega) :
    Hstep H (tagInj 2 x) t = hSucc H (tagInj 2 x) t := by
  simp only [Hstep, expTag, tagInj.zero, predSet.ofNat_succ,
    dcondSet.ofNat_succ, dcondSet.ofNat_zero]

theorem tag3 (H x t : Pomega) :
    Hstep H (tagInj 3 x) t = hPred H (tagInj 3 x) t := by
  simp only [Hstep, expTag, tagInj.zero, dcondSet.ofNat_succ,
    predSet.ofNat_succ, PlotkinHelpers.predSet_iterate_self,
    dcondSet.ofNat_zero]

theorem tag4 (H x t : Pomega) :
    Hstep H (tagInj 4 x) t = hCond H (tagInj 4 x) t := by
  simp only [Hstep, expTag, tagInj.zero, dcondSet.ofNat_succ,
    predSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 3) (i := 1),
    PlotkinHelpers.predSet_iterate_self, dcondSet.ofNat_zero]

theorem tag5 (H x t : Pomega) :
    Hstep H (tagInj 5 x) t = hApp H (tagInj 5 x) t := by
  simp only [Hstep, expTag, tagInj.zero, dcondSet.ofNat_succ,
    predSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 3) (i := 2),
    PlotkinHelpers.predSet_iterate_ofNat (k := 4) (i := 1),
    PlotkinHelpers.predSet_iterate_self, dcondSet.ofNat_zero]

theorem tag6 (H x t : Pomega) :
    Hstep H (tagInj 6 x) t = hLam H (tagInj 6 x) t := by
  simp only [Hstep, expTag, tagInj.zero, dcondSet.ofNat_succ,
    predSet.ofNat_succ, PlotkinHelpers.predSet_iterate_ofNat (k := 3) (i := 3),
    PlotkinHelpers.predSet_iterate_ofNat (k := 4) (i := 2),
    PlotkinHelpers.predSet_iterate_ofNat (k := 5) (i := 1),
    PlotkinHelpers.predSet_iterate_self, dcondSet.ofNat_zero]

theorem isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => Hstep H e t) :=
  ContinuityHelpers.nary
    (fun y z => dcondSet.isScottContinuous_left y z)
    (fun x z => dcondSet.isScottContinuous_mid x z)
    (fun x y => dcondSet.isScottContinuous_right x y)
    (const_isScottContinuous (expTag e)) (const_isScottContinuous (hVar e t))
    (ContinuityHelpers.nary
      (fun y z => dcondSet.isScottContinuous_left y z)
      (fun x z => dcondSet.isScottContinuous_mid x z)
      (fun x y => dcondSet.isScottContinuous_right x y)
      (const_isScottContinuous (predSet (expTag e)))
      (const_isScottContinuous hZero)
      (ContinuityHelpers.nary
        (fun y z => dcondSet.isScottContinuous_left y z)
        (fun x z => dcondSet.isScottContinuous_mid x z)
        (fun x y => dcondSet.isScottContinuous_right x y)
        (const_isScottContinuous (predSet (predSet (expTag e))))
        (hSucc.isScottContinuous_H e t)
        (ContinuityHelpers.nary
          (fun y z => dcondSet.isScottContinuous_left y z)
          (fun x z => dcondSet.isScottContinuous_mid x z)
          (fun x y => dcondSet.isScottContinuous_right x y)
          (const_isScottContinuous (predSet^[3] (expTag e)))
          (hPred.isScottContinuous_H e t)
          (ContinuityHelpers.nary
            (fun y z => dcondSet.isScottContinuous_left y z)
            (fun x z => dcondSet.isScottContinuous_mid x z)
            (fun x y => dcondSet.isScottContinuous_right x y)
            (const_isScottContinuous (predSet^[4] (expTag e)))
            (hCond.isScottContinuous_H e t)
            (ContinuityHelpers.nary
              (fun y z => dcondSet.isScottContinuous_left y z)
              (fun x z => dcondSet.isScottContinuous_mid x z)
              (fun x y => dcondSet.isScottContinuous_right x y)
              (const_isScottContinuous (predSet^[5] (expTag e)))
              (hApp.isScottContinuous_H e t)
              (ContinuityHelpers.nary
                (fun y z => dcondSet.isScottContinuous_left y z)
                (fun x z => dcondSet.isScottContinuous_mid x z)
                (fun x y => dcondSet.isScottContinuous_right x y)
                (const_isScottContinuous (predSet^[6] (expTag e)))
                (hLam.isScottContinuous_H e t)
                (const_isScottContinuous topElem)))))))

theorem isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => Hstep H e t) :=
  ContinuityHelpers.nary
    (fun y z => dcondSet.isScottContinuous_left y z)
    (fun x z => dcondSet.isScottContinuous_mid x z)
    (fun x y => dcondSet.isScottContinuous_right x y)
    (const_isScottContinuous (expTag e))
    (hVar.isScottContinuous_t e)
    (ContinuityHelpers.nary
      (fun y z => dcondSet.isScottContinuous_left y z)
      (fun x z => dcondSet.isScottContinuous_mid x z)
      (fun x y => dcondSet.isScottContinuous_right x y)
      (const_isScottContinuous (predSet (expTag e)))
      (const_isScottContinuous hZero)
      (ContinuityHelpers.nary
        (fun y z => dcondSet.isScottContinuous_left y z)
        (fun x z => dcondSet.isScottContinuous_mid x z)
        (fun x y => dcondSet.isScottContinuous_right x y)
        (const_isScottContinuous (predSet (predSet (expTag e))))
        (hSucc.isScottContinuous_t H e)
        (ContinuityHelpers.nary
          (fun y z => dcondSet.isScottContinuous_left y z)
          (fun x z => dcondSet.isScottContinuous_mid x z)
          (fun x y => dcondSet.isScottContinuous_right x y)
          (const_isScottContinuous (predSet^[3] (expTag e)))
          (hPred.isScottContinuous_t H e)
          (ContinuityHelpers.nary
            (fun y z => dcondSet.isScottContinuous_left y z)
            (fun x z => dcondSet.isScottContinuous_mid x z)
            (fun x y => dcondSet.isScottContinuous_right x y)
            (const_isScottContinuous (predSet^[4] (expTag e)))
            (hCond.isScottContinuous_t H e)
            (ContinuityHelpers.nary
              (fun y z => dcondSet.isScottContinuous_left y z)
              (fun x z => dcondSet.isScottContinuous_mid x z)
              (fun x y => dcondSet.isScottContinuous_right x y)
              (const_isScottContinuous (predSet^[5] (expTag e)))
              (hApp.isScottContinuous_t H e)
              (ContinuityHelpers.nary
                (fun y z => dcondSet.isScottContinuous_left y z)
                (fun x z => dcondSet.isScottContinuous_mid x z)
                (fun x y => dcondSet.isScottContinuous_right x y)
                (const_isScottContinuous (predSet^[6] (expTag e)))
                (hLam.isScottContinuous_t H e)
                (const_isScottContinuous topElem)))))))

theorem isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => Hstep H e t) :=
  ContinuityHelpers.nary
    (fun y z => dcondSet.isScottContinuous_left y z)
    (fun x z => dcondSet.isScottContinuous_mid x z)
    (fun x y => dcondSet.isScottContinuous_right x y)
    (funOf.isScottContinuous_left (ofNat 0))
    (hVar.isScottContinuous_e t)
    (ContinuityHelpers.nary
      (fun y z => dcondSet.isScottContinuous_left y z)
      (fun x z => dcondSet.isScottContinuous_mid x z)
      (fun x y => dcondSet.isScottContinuous_right x y)
      (PlotkinHelpers.predSet_iterate_expTag_isScottContinuous 1)
      (const_isScottContinuous hZero)
      (ContinuityHelpers.nary
        (fun y z => dcondSet.isScottContinuous_left y z)
        (fun x z => dcondSet.isScottContinuous_mid x z)
        (fun x y => dcondSet.isScottContinuous_right x y)
        (PlotkinHelpers.predSet_iterate_expTag_isScottContinuous 2)
        (hSucc.isScottContinuous_e H t)
        (ContinuityHelpers.nary
          (fun y z => dcondSet.isScottContinuous_left y z)
          (fun x z => dcondSet.isScottContinuous_mid x z)
          (fun x y => dcondSet.isScottContinuous_right x y)
          (PlotkinHelpers.predSet_iterate_expTag_isScottContinuous 3)
          (hPred.isScottContinuous_e H t)
          (ContinuityHelpers.nary
            (fun y z => dcondSet.isScottContinuous_left y z)
            (fun x z => dcondSet.isScottContinuous_mid x z)
            (fun x y => dcondSet.isScottContinuous_right x y)
            (PlotkinHelpers.predSet_iterate_expTag_isScottContinuous 4)
            (hCond.isScottContinuous_e H t)
            (ContinuityHelpers.nary
              (fun y z => dcondSet.isScottContinuous_left y z)
              (fun x z => dcondSet.isScottContinuous_mid x z)
              (fun x y => dcondSet.isScottContinuous_right x y)
              (PlotkinHelpers.predSet_iterate_expTag_isScottContinuous 5)
              (hApp.isScottContinuous_e H t)
              (ContinuityHelpers.nary
                (fun y z => dcondSet.isScottContinuous_left y z)
                (fun x z => dcondSet.isScottContinuous_mid x z)
                (fun x y => dcondSet.isScottContinuous_right x y)
                (PlotkinHelpers.predSet_iterate_expTag_isScottContinuous 6)
                (hLam.isScottContinuous_e H t)
                (const_isScottContinuous topElem)))))))
end Hstep


def HF (H : Pomega) : Pomega :=
  graph (fun e => graph (fun t => Hstep H e t))

namespace HF

theorem inner_isScottContinuous (H : Pomega) :
    IsScottContinuous (fun e => graph (fun t => Hstep H e t)) :=
  graph_const_isScottContinuous (fun e t => Hstep H e t)
    (fun t => Hstep.isScottContinuous_e H t)

theorem isScottContinuous : IsScottContinuous HF :=
  graph_const_isScottContinuous
    (fun H e => graph (fun t => Hstep H e t))
    (fun e => graph_const_isScottContinuous (fun H t => Hstep H e t)
      (fun t => Hstep.isScottContinuous_H e t))

theorem app (H e : Pomega) :
    funOf (HF H) e = graph (fun t => Hstep H e t) :=
  beta (HF.inner_isScottContinuous H) e

theorem app2 (H e t : Pomega) :
    funOf (funOf (HF H) e) t = Hstep H e t := by
  rw [HF.app]
  exact beta (Hstep.isScottContinuous_t H e) t

end HF


def Hinterp : LambTerm → Pomega → Pomega
  | .var n, t => funOf t (ofNat n)
  | .zero, _ => funOf inleftC (ofNat 0)
  | .succ τ, t =>
      condSet (funOf whichC (Hinterp τ t))
        (funOf inleftC (succSet (funOf outC (Hinterp τ t))))
        botElem
  | .pred τ, t =>
      condSet (funOf whichC (Hinterp τ t))
        (funOf inleftC (predSet (funOf outC (Hinterp τ t))))
        botElem
  | .condq θ τ σ ρ, t =>
      funOf lambR (condSet (funOf whichC (Hinterp θ t))
        (condSet (funOf outC (Hinterp θ t)) (Hinterp τ t) (Hinterp σ t))
        (Hinterp ρ t))
  | .app τ σ, t =>
      condSet (funOf whichC (Hinterp τ t)) botElem
        (funOf (funOf outC (Hinterp τ t)) (Hinterp σ t))
  | .lam n τ, t =>
      funOf inrightC (graph (fun x => Hinterp τ (updateEnv t x n)))

namespace Hinterp

theorem isScottContinuous (τ : LambTerm) :
    IsScottContinuous (Hinterp τ) := by
  induction τ with
  | var n =>
    exact funOf.isScottContinuous_left (ofNat n)
  | zero =>
    exact const_isScottContinuous _
  | succ τ ih =>
    exact ContinuityHelpers.nary
      (fun y z => condSet.isScottContinuous_left y z)
      (fun x z => condSet.isScottContinuous_mid x z)
      (fun x y => condSet.isScottContinuous_right x y)
      (theorem_1_3 (funOf.isScottContinuous whichC) ih)
      (theorem_1_3 (funOf.isScottContinuous inleftC)
        (theorem_1_3 succSet.isScottContinuous
          (theorem_1_3 (funOf.isScottContinuous outC) ih)))
      (const_isScottContinuous botElem)
  | pred τ ih =>
    exact ContinuityHelpers.nary
      (fun y z => condSet.isScottContinuous_left y z)
      (fun x z => condSet.isScottContinuous_mid x z)
      (fun x y => condSet.isScottContinuous_right x y)
      (theorem_1_3 (funOf.isScottContinuous whichC) ih)
      (theorem_1_3 (funOf.isScottContinuous inleftC)
        (theorem_1_3 predSet.isScottContinuous
          (theorem_1_3 (funOf.isScottContinuous outC) ih)))
      (const_isScottContinuous botElem)
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    exact theorem_1_3 (f := funOf lambR)
      (g := fun t =>
        condSet (funOf whichC (Hinterp θ t))
          (condSet (funOf outC (Hinterp θ t)) (Hinterp τ t) (Hinterp σ t))
          (Hinterp ρ t))
      (funOf.isScottContinuous lambR)
      (ContinuityHelpers.nary
        (fun y z => condSet.isScottContinuous_left y z)
        (fun x z => condSet.isScottContinuous_mid x z)
        (fun x y => condSet.isScottContinuous_right x y)
        (theorem_1_3 (funOf.isScottContinuous whichC) ihθ)
        (ContinuityHelpers.nary
          (fun y z => condSet.isScottContinuous_left y z)
          (fun x z => condSet.isScottContinuous_mid x z)
          (fun x y => condSet.isScottContinuous_right x y)
          (theorem_1_3 (funOf.isScottContinuous outC) ihθ) ihτ ihσ)
        ihρ)
  | app τ σ ihτ ihσ =>
    exact ContinuityHelpers.nary
      (fun y z => condSet.isScottContinuous_left y z)
      (fun x z => condSet.isScottContinuous_mid x z)
      (fun x y => condSet.isScottContinuous_right x y)
      (theorem_1_3 (funOf.isScottContinuous whichC) ihτ)
      (const_isScottContinuous botElem)
      (ContinuityHelpers.tuple
        (fun y => funOf.isScottContinuous_left y)
        (fun u => funOf.isScottContinuous u)
        (theorem_1_3 (funOf.isScottContinuous outC) ihτ) ihσ)
  | lam n τ ih =>
    exact theorem_1_3 (f := funOf inrightC)
      (g := fun t => graph (fun x => Hinterp τ (updateEnv t x n)))
      (funOf.isScottContinuous inrightC)
      (graph_const_isScottContinuous
        (fun t x => Hinterp τ (updateEnv t x n))
        (fun x => theorem_1_3 ih
          (graph_const_isScottContinuous
            (fun t m => if m = ofNat n then x else funOf t m)
            (fun m => by
              by_cases h : m = ofNat n
              · simpa [h] using const_isScottContinuous (c := x)
              · simpa [h] using funOf.isScottContinuous_left m))))

end Hinterp


def Hfun : Pomega := fix HF

namespace Hfun

theorem fixed : HF Hfun = Hfun :=
  (theorem_1_4 HF.isScottContinuous).1

theorem app2 (e t : Pomega) :
    funOf (funOf Hfun e) t = Hstep Hfun e t := by
  have h := congrArg (fun H => funOf (funOf H e) t) fixed
  simpa [HF.app2] using h.symm

theorem interp : ∀ τ : LambTerm, ∀ t : Pomega,
    funOf (funOf Hfun (encodeExp τ)) t = Hinterp τ t := by
  intro τ
  induction τ with
  | var n =>
    intro t
    rw [app2, encodeExp, Hstep.tag0]
    rfl
  | zero =>
    intro t
    rw [app2, encodeExp, Hstep.tag1]
    rfl
  | succ τ ih =>
    intro t
    rw [app2, encodeExp, Hstep.tag2]
    simp only [hSucc, hApply, expPayload, tagInj.one]
    rw [ih]
    rfl
  | pred τ ih =>
    intro t
    rw [app2, encodeExp, Hstep.tag3]
    simp only [hPred, hApply, expPayload, tagInj.one]
    rw [ih]
    rfl
  | condq θ τ σ ρ ihθ ihτ ihσ ihρ =>
    intro t
    rw [app2, encodeExp, Hstep.tag4]
    simp only [hCond, hApply, expPayload, tagInj.one, seq4.zero,
      seq4.one, seq4.two, seq4.three]
    rw [ihθ, ihτ, ihσ, ihρ]
    rfl
  | app τ σ ihτ ihσ =>
    intro t
    rw [app2, encodeExp, Hstep.tag5]
    simp only [hApp, hApply, expPayload, tagInj.one, PairSeq.app_zero,
      PairSeq.app_one]
    rw [ihτ, ihσ]
    rfl
  | lam n τ ih =>
    intro t
    rw [app2, encodeExp, Hstep.tag6]
    simp only [hLam, hApply, expPayload, tagInj.one, PairSeq.app_zero,
      PairSeq.app_one, updateEnv.ofNat]
    congr 1
    apply congrArg graph
    funext x
    exact ih _

theorem decode (τ : LambTerm) :
    funOf Hfun (encodeExp τ) = graph (Hinterp τ) := by
  have hβ : funOf Hfun (encodeExp τ) = graph (fun t => Hstep Hfun (encodeExp τ) t) := by
    have := congrArg (fun H => funOf H (encodeExp τ)) fixed
    simpa [HF.app] using this.symm
  refine hβ.trans ?_
  apply congrArg graph
  funext t
  simpa [app2] using interp τ t

end Hfun


def Htyped (τ : LambTerm) : Pomega :=
  funOf (arrowR envR lambR) (graph (Hinterp τ))

namespace Htyped

theorem app (τ : LambTerm) (t : Pomega) :
    funOf (Htyped τ) t = funOf lambR (Hinterp τ (funOf envR t)) := by
  rw [Htyped, arrowR.app]
  simp only [comp.app]
  apply congrArg (funOf lambR)
  exact beta (Hinterp.isScottContinuous τ) (funOf envR t)

theorem typed (τ : LambTerm) :
    typed (Htyped τ) (arrowR envR lambR) :=
  typed.apply_retract
    (arrowR.isRetract envR.isRetract lambR.isRetract)

end Htyped


def Hcomb : Pomega :=
  funOf (arrowR expR (arrowR envR lambR)) Hfun

namespace Hcomb

theorem app (e : Pomega) :
    funOf Hcomb e =
      funOf (arrowR envR lambR) (funOf Hfun (funOf expR e)) := by
  rw [Hcomb, arrowR.app]
  simp only [comp.app]

theorem typed :
    typed Hcomb (arrowR expR (arrowR envR lambR)) :=
  typed.apply_retract
    (arrowR.isRetract expR.isRetract
      (arrowR.isRetract envR.isRetract lambR.isRetract))

end Hcomb


theorem eq_4_45 (τ : LambTerm) :
    typed (encodeExp τ) expR ∧
      typed (Htyped τ) (arrowR envR lambR) ∧
        funOf Hcomb (encodeExp τ) = Htyped τ := by
  refine ⟨encodeExp.typed τ, Htyped.typed τ, ?_⟩
  rw [Hcomb.app, ← encodeExp.typed τ, Hfun.decode]
  rfl

end DomainTheory.DataTypesAsLattices
