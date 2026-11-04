module

public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Functionality.ContinuityHelpers
public import DomainTheory.DataTypesAsLattices.Functionality.encodeExp
public import DomainTheory.DataTypesAsLattices.Functionality.CombC
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Lambda.Language
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_more
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.lambR
public import DomainTheory.DataTypesAsLattices.Retracts.updateEnv
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

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


end DomainTheory.DataTypesAsLattices
