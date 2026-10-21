/-ai
For each v, the body of vaalF is Scott continuous. That body sends x to the McCarthy conditional of the application of x to zero, with zero branch the G combinator and positive branch the application of v at the left child of x to the application of v at the right child.

The n-ary continuity law is applied to continuity of the conditional in its test, in its zero branch, and in its positive branch, to continuity of application in the function at the numeral zero, to the constant map at the G combinator, and to the nested application. The nested application is a continuous pairing of application in the function with application in the argument. Theorem 1.3 forms each child from the continuous application of v after the continuous composite of application at zero, or at one, following application at one.
ai-/
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
