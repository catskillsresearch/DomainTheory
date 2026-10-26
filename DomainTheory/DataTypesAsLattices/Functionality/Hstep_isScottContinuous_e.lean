module

public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.hZero
public import DomainTheory.DataTypesAsLattices.Functionality.hSucc
public import DomainTheory.DataTypesAsLattices.Functionality.hLam
public import DomainTheory.DataTypesAsLattices.Functionality.Hstep
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.hVar_isScottContinuous_e
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_expTag_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.hPred_isScottContinuous_e
public import DomainTheory.DataTypesAsLattices.Functionality.hCond_isScottContinuous_e
public import DomainTheory.DataTypesAsLattices.Functionality.hApp
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_more
public import DomainTheory.DataTypesAsLattices.Functionality.hLam_isScottContinuous_e
public import DomainTheory.DataTypesAsLattices.Functionality.hSucc_isScottContinuous_e

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Hstep.isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => Hstep H e t) :=
  continuous_nary
    (fun y z => dcondSet.isScottContinuous_left y z)
    (fun x z => dcondSet.isScottContinuous_mid x z)
    (fun x y => dcondSet.isScottContinuous_right x y)
    (funOf.isScottContinuous_left (ofNat 0))
    (hVar_isScottContinuous_e t)
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
          (hPred_isScottContinuous_e H t)
          (continuous_nary
            (fun y z => dcondSet.isScottContinuous_left y z)
            (fun x z => dcondSet.isScottContinuous_mid x z)
            (fun x y => dcondSet.isScottContinuous_right x y)
            (predSet_iterate_expTag_isScottContinuous 4)
            (hCond_isScottContinuous_e H t)
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

end DomainTheory.DataTypesAsLattices
