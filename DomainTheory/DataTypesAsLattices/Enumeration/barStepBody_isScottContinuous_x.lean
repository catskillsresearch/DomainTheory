module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos_isScottContinuous_x

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem barStepBody_isScottContinuous_x (B u : Pomega) :
    IsScottContinuous (fun x => barStepBody B u x) :=
  theorem_1_3_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun tes z => condSet_isScottContinuous_mid tes z)
    (fun tes th => condSet_isScottContinuous_right tes th)
    (funOf_isScottContinuous_left (ofNat 0))
    (barPos_isScottContinuous_x u)
    (theorem_1_3_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun w => funOf_isScottContinuous w)
      (theorem_1_3 (funOf_isScottContinuous B)
        (theorem_1_3 (funOf_isScottContinuous u)
          (funOf_isScottContinuous_left (ofNat 1))))
      (funOf_isScottContinuous_left (ofNat 2)))

end DomainTheory.DataTypesAsLattices
