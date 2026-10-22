/-ai
Applying L to x returns the application of x at the numeral 1, applied to the application of x at the numeral 2.

This is the beta law for the graph of that map. Its Scott continuity is the tuple form of Theorem 1.3 applied to continuity of application in the function argument, continuity of application, and continuity of application to the fixed numerals 1 and 2.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem Lcomb_app (x : Pomega) :
    funOf Lcomb x = funOf (funOf x (ofNat 1)) (funOf x (ofNat 2)) :=
  beta (theorem_1_3_tuple
    (fun y => funOf_isScottContinuous_left y)
    (fun t => funOf_isScottContinuous t)
    (funOf_isScottContinuous_left (ofNat 1))
    (funOf_isScottContinuous_left (ofNat 2))) x

end DomainTheory.DataTypesAsLattices
