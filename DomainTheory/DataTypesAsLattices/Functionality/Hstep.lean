module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.expPayload
public import DomainTheory.DataTypesAsLattices.Functionality.expTag
public import DomainTheory.DataTypesAsLattices.Functionality.hApp
public import DomainTheory.DataTypesAsLattices.Functionality.hCond
public import DomainTheory.DataTypesAsLattices.Functionality.hLam
public import DomainTheory.DataTypesAsLattices.Functionality.hPred
public import DomainTheory.DataTypesAsLattices.Functionality.hSucc
public import DomainTheory.DataTypesAsLattices.Functionality.hVar
public import DomainTheory.DataTypesAsLattices.Functionality.hZero
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_expTag_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_ofNat
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_self
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_more
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.tagInj
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

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
  simp only [Hstep, expTag, expPayload, hVar, tagInj_zero, tagInj_one,
    dcondSet.ofNat_zero]

theorem tag1 (H x t : Pomega) :
    Hstep H (tagInj 1 x) t = hZero := by
  simp only [Hstep, expTag, tagInj_zero, predSet.ofNat_succ,
    dcondSet.ofNat_one, dcondSet.ofNat_zero]

theorem tag2 (H x t : Pomega) :
    Hstep H (tagInj 2 x) t = hSucc H (tagInj 2 x) t := by
  simp only [Hstep, expTag, tagInj_zero, predSet.ofNat_succ,
    dcondSet.ofNat_succ, dcondSet.ofNat_zero]

theorem tag3 (H x t : Pomega) :
    Hstep H (tagInj 3 x) t = hPred H (tagInj 3 x) t := by
  simp only [Hstep, expTag, tagInj_zero, dcondSet.ofNat_succ,
    predSet.ofNat_succ, predSet_iterate_self,
    dcondSet.ofNat_zero]

theorem tag4 (H x t : Pomega) :
    Hstep H (tagInj 4 x) t = hCond H (tagInj 4 x) t := by
  simp only [Hstep, expTag, tagInj_zero, dcondSet.ofNat_succ,
    predSet.ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 1),
    predSet_iterate_self, dcondSet.ofNat_zero]

theorem tag5 (H x t : Pomega) :
    Hstep H (tagInj 5 x) t = hApp H (tagInj 5 x) t := by
  simp only [Hstep, expTag, tagInj_zero, dcondSet.ofNat_succ,
    predSet.ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 2),
    predSet_iterate_ofNat (k := 4) (i := 1),
    predSet_iterate_self, dcondSet.ofNat_zero]

theorem tag6 (H x t : Pomega) :
    Hstep H (tagInj 6 x) t = hLam H (tagInj 6 x) t := by
  simp only [Hstep, expTag, tagInj_zero, dcondSet.ofNat_succ,
    predSet.ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 3),
    predSet_iterate_ofNat (k := 4) (i := 2),
    predSet_iterate_ofNat (k := 5) (i := 1),
    predSet_iterate_self, dcondSet.ofNat_zero]

theorem isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => Hstep H e t) :=
  continuous_nary
    (fun y z => dcondSet.isScottContinuous_left y z)
    (fun x z => dcondSet.isScottContinuous_mid x z)
    (fun x y => dcondSet.isScottContinuous_right x y)
    (const_isScottContinuous (expTag e)) (const_isScottContinuous (hVar e t))
    (continuous_nary
      (fun y z => dcondSet.isScottContinuous_left y z)
      (fun x z => dcondSet.isScottContinuous_mid x z)
      (fun x y => dcondSet.isScottContinuous_right x y)
      (const_isScottContinuous (predSet (expTag e)))
      (const_isScottContinuous hZero)
      (continuous_nary
        (fun y z => dcondSet.isScottContinuous_left y z)
        (fun x z => dcondSet.isScottContinuous_mid x z)
        (fun x y => dcondSet.isScottContinuous_right x y)
        (const_isScottContinuous (predSet (predSet (expTag e))))
        (hSucc.isScottContinuous_H e t)
        (continuous_nary
          (fun y z => dcondSet.isScottContinuous_left y z)
          (fun x z => dcondSet.isScottContinuous_mid x z)
          (fun x y => dcondSet.isScottContinuous_right x y)
          (const_isScottContinuous (predSet^[3] (expTag e)))
          (hPred.isScottContinuous_H e t)
          (continuous_nary
            (fun y z => dcondSet.isScottContinuous_left y z)
            (fun x z => dcondSet.isScottContinuous_mid x z)
            (fun x y => dcondSet.isScottContinuous_right x y)
            (const_isScottContinuous (predSet^[4] (expTag e)))
            (hCond.isScottContinuous_H e t)
            (continuous_nary
              (fun y z => dcondSet.isScottContinuous_left y z)
              (fun x z => dcondSet.isScottContinuous_mid x z)
              (fun x y => dcondSet.isScottContinuous_right x y)
              (const_isScottContinuous (predSet^[5] (expTag e)))
              (hApp.isScottContinuous_H e t)
              (continuous_nary
                (fun y z => dcondSet.isScottContinuous_left y z)
                (fun x z => dcondSet.isScottContinuous_mid x z)
                (fun x y => dcondSet.isScottContinuous_right x y)
                (const_isScottContinuous (predSet^[6] (expTag e)))
                (hLam.isScottContinuous_H e t)
                (const_isScottContinuous topElem)))))))

theorem isScottContinuous_t (H e : Pomega) :
    IsScottContinuous (fun t => Hstep H e t) :=
  continuous_nary
    (fun y z => dcondSet.isScottContinuous_left y z)
    (fun x z => dcondSet.isScottContinuous_mid x z)
    (fun x y => dcondSet.isScottContinuous_right x y)
    (const_isScottContinuous (expTag e))
    (hVar.isScottContinuous_t e)
    (continuous_nary
      (fun y z => dcondSet.isScottContinuous_left y z)
      (fun x z => dcondSet.isScottContinuous_mid x z)
      (fun x y => dcondSet.isScottContinuous_right x y)
      (const_isScottContinuous (predSet (expTag e)))
      (const_isScottContinuous hZero)
      (continuous_nary
        (fun y z => dcondSet.isScottContinuous_left y z)
        (fun x z => dcondSet.isScottContinuous_mid x z)
        (fun x y => dcondSet.isScottContinuous_right x y)
        (const_isScottContinuous (predSet (predSet (expTag e))))
        (hSucc.isScottContinuous_t H e)
        (continuous_nary
          (fun y z => dcondSet.isScottContinuous_left y z)
          (fun x z => dcondSet.isScottContinuous_mid x z)
          (fun x y => dcondSet.isScottContinuous_right x y)
          (const_isScottContinuous (predSet^[3] (expTag e)))
          (hPred.isScottContinuous_t H e)
          (continuous_nary
            (fun y z => dcondSet.isScottContinuous_left y z)
            (fun x z => dcondSet.isScottContinuous_mid x z)
            (fun x y => dcondSet.isScottContinuous_right x y)
            (const_isScottContinuous (predSet^[4] (expTag e)))
            (hCond.isScottContinuous_t H e)
            (continuous_nary
              (fun y z => dcondSet.isScottContinuous_left y z)
              (fun x z => dcondSet.isScottContinuous_mid x z)
              (fun x y => dcondSet.isScottContinuous_right x y)
              (const_isScottContinuous (predSet^[5] (expTag e)))
              (hApp.isScottContinuous_t H e)
              (continuous_nary
                (fun y z => dcondSet.isScottContinuous_left y z)
                (fun x z => dcondSet.isScottContinuous_mid x z)
                (fun x y => dcondSet.isScottContinuous_right x y)
                (const_isScottContinuous (predSet^[6] (expTag e)))
                (hLam.isScottContinuous_t H e)
                (const_isScottContinuous topElem)))))))

theorem isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => Hstep H e t) :=
  continuous_nary
    (fun y z => dcondSet.isScottContinuous_left y z)
    (fun x z => dcondSet.isScottContinuous_mid x z)
    (fun x y => dcondSet.isScottContinuous_right x y)
    (funOf.isScottContinuous_left (ofNat 0))
    (hVar.isScottContinuous_e t)
    (continuous_nary
      (fun y z => dcondSet.isScottContinuous_left y z)
      (fun x z => dcondSet.isScottContinuous_mid x z)
      (fun x y => dcondSet.isScottContinuous_right x y)
      (predSet_iterate_expTag_isScottContinuous 1)
      (const_isScottContinuous hZero)
      (continuous_nary
        (fun y z => dcondSet.isScottContinuous_left y z)
        (fun x z => dcondSet.isScottContinuous_mid x z)
        (fun x y => dcondSet.isScottContinuous_right x y)
        (predSet_iterate_expTag_isScottContinuous 2)
        (hSucc.isScottContinuous_e H t)
        (continuous_nary
          (fun y z => dcondSet.isScottContinuous_left y z)
          (fun x z => dcondSet.isScottContinuous_mid x z)
          (fun x y => dcondSet.isScottContinuous_right x y)
          (predSet_iterate_expTag_isScottContinuous 3)
          (hPred.isScottContinuous_e H t)
          (continuous_nary
            (fun y z => dcondSet.isScottContinuous_left y z)
            (fun x z => dcondSet.isScottContinuous_mid x z)
            (fun x y => dcondSet.isScottContinuous_right x y)
            (predSet_iterate_expTag_isScottContinuous 4)
            (hCond.isScottContinuous_e H t)
            (continuous_nary
              (fun y z => dcondSet.isScottContinuous_left y z)
              (fun x z => dcondSet.isScottContinuous_mid x z)
              (fun x y => dcondSet.isScottContinuous_right x y)
              (predSet_iterate_expTag_isScottContinuous 5)
              (hApp.isScottContinuous_e H t)
              (continuous_nary
                (fun y z => dcondSet.isScottContinuous_left y z)
                (fun x z => dcondSet.isScottContinuous_mid x z)
                (fun x y => dcondSet.isScottContinuous_right x y)
                (predSet_iterate_expTag_isScottContinuous 6)
                (hLam.isScottContinuous_e H t)
                (const_isScottContinuous topElem)))))))
end Hstep

end DomainTheory.DataTypesAsLattices
