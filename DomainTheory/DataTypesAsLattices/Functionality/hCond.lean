module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.expPayload
public import DomainTheory.DataTypesAsLattices.Functionality.hApply
public import DomainTheory.DataTypesAsLattices.Functionality.outC
public import DomainTheory.DataTypesAsLattices.Functionality.whichC
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.lambR

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

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
    (continuous_nary
      (fun y z => condSet.isScottContinuous_left y z)
      (fun x z => condSet.isScottContinuous_mid x z)
      (fun x y => condSet.isScottContinuous_right x y)
      (theorem_1_3 (funOf.isScottContinuous whichC)
        (hApply.isScottContinuous_H _ t))
      (continuous_nary
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
    (continuous_nary
      (fun y z => condSet.isScottContinuous_left y z)
      (fun x z => condSet.isScottContinuous_mid x z)
      (fun x y => condSet.isScottContinuous_right x y)
      (theorem_1_3 (f := funOf whichC)
        (g := fun t => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf.isScottContinuous whichC)
        (funOf.isScottContinuous (funOf H (funOf (expPayload e) (ofNat 0)))))
      (continuous_nary
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
    (continuous_nary
      (fun y z => condSet.isScottContinuous_left y z)
      (fun x z => condSet.isScottContinuous_mid x z)
      (fun x y => condSet.isScottContinuous_right x y)
      (theorem_1_3 (f := funOf whichC)
        (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf.isScottContinuous whichC)
        (hApply.payload_isScottContinuous_e H t 0))
      (continuous_nary
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

end DomainTheory.DataTypesAsLattices
