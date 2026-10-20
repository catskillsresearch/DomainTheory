module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.hApply_payload_isScottContinuous_e

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem hApp_isScottContinuous_e (H t : Pomega) :
    IsScottContinuous (fun e => hApp H e t) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (theorem_1_3 (f := funOf whichC)
      (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
      (funOf_isScottContinuous whichC)
      (hApply_payload_isScottContinuous_e H t 0))
    (const_isScottContinuous botElem)
    (continuous_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun u => funOf_isScottContinuous u)
      (theorem_1_3 (f := funOf outC)
        (g := fun e => hApply H (funOf (expPayload e) (ofNat 0)) t)
        (funOf_isScottContinuous outC)
        (hApply_payload_isScottContinuous_e H t 0))
      (hApply_payload_isScottContinuous_e H t 1))

end DomainTheory.DataTypesAsLattices
