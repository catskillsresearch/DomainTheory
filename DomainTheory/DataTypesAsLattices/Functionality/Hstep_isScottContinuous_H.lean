module

public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.expTag
public import DomainTheory.DataTypesAsLattices.Functionality.hVar
public import DomainTheory.DataTypesAsLattices.Functionality.hZero
public import DomainTheory.DataTypesAsLattices.Functionality.hSucc
public import DomainTheory.DataTypesAsLattices.Functionality.hLam
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.hPred_isScottContinuous_H
public import DomainTheory.DataTypesAsLattices.Functionality.hCond_isScottContinuous_H
public import DomainTheory.DataTypesAsLattices.Functionality.hApp
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_more
public import DomainTheory.DataTypesAsLattices.Functionality.hLam
public import DomainTheory.DataTypesAsLattices.Functionality.hSucc_isScottContinuous_H

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Hstep.isScottContinuous_H (e t : Pomega) :
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
          (hPred_isScottContinuous_H e t)
          (continuous_nary
            (fun y z => dcondSet.isScottContinuous_left y z)
            (fun x z => dcondSet.isScottContinuous_mid x z)
            (fun x y => dcondSet.isScottContinuous_right x y)
            (const_isScottContinuous (predSet^[4] (expTag e)))
            (hCond_isScottContinuous_H e t)
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

end DomainTheory.DataTypesAsLattices
