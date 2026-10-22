/-ai
For fixed B and x, the bar step body is Scott continuous in u.

Binary substitution uses middle and right continuity of the conditional at the application of x to the numeral 0, continuity of the positive branch in its first argument at x, and the composite of left application at the application of x to the numeral 2 with the substitution of continuity of application of B into left application at the application of x to the numeral 1.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos_isScottContinuous_u

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem barStepBody_isScottContinuous_u (B x : Pomega) :
    IsScottContinuous (fun u => barStepBody B u x) :=
  theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_mid (funOf x (ofNat 0)) y)
    (fun w => condSet_isScottContinuous_right (funOf x (ofNat 0)) w)
    (barPos_isScottContinuous_u x)
    (theorem_1_3
      (f := fun w => funOf w (funOf x (ofNat 2)))
      (g := fun u => funOf B (funOf u (funOf x (ofNat 1))))
      (funOf_isScottContinuous_left (funOf x (ofNat 2)))
      (theorem_1_3 (funOf_isScottContinuous B)
        (funOf_isScottContinuous_left (funOf x (ofNat 1)))))

end DomainTheory.DataTypesAsLattices
