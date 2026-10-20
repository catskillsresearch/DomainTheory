module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code
























































theorem vaalF_body_isScottContinuous (v : Pomega) :
    IsScottContinuous (fun x =>
      condSet (funOf x (ofNat 0)) Gcomb
        (funOf (funOf v (funOf (funOf x (ofNat 1)) (ofNat 0)))
          (funOf v (funOf (funOf x (ofNat 1)) (ofNat 1))))) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (funOf_isScottContinuous_left (ofNat 0))
    (const_isScottContinuous Gcomb)
    (continuous_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun u => funOf_isScottContinuous u)
      (theorem_1_3 (funOf_isScottContinuous v)
        (theorem_1_3
          (f := fun u => funOf u (ofNat 0))
          (g := fun x => funOf x (ofNat 1))
          (funOf_isScottContinuous_left (ofNat 0))
          (funOf_isScottContinuous_left (ofNat 1))))
      (theorem_1_3 (funOf_isScottContinuous v)
        (theorem_1_3
          (f := fun u => funOf u (ofNat 1))
          (g := fun x => funOf x (ofNat 1))
          (funOf_isScottContinuous_left (ofNat 1))
          (funOf_isScottContinuous_left (ofNat 1)))))

end DomainTheory.DataTypesAsLattices
