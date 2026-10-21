/-ai
For fixed u and x, the bar step body is Scott continuous in B.

The substitution theorem applies right continuity of the conditional, taken at the application of x to the numeral 0 and at the positive branch of u and x, to the composite of left application at the application of x to the numeral 2 with left application at the application of u to the application of x to the numeral 1.
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
















































theorem barStepBody_isScottContinuous_B (u x : Pomega) :
    IsScottContinuous (fun B => barStepBody B u x) :=
  theorem_1_3 (condSet_isScottContinuous_right (funOf x (ofNat 0)) (barPos u x))
    (theorem_1_3
      (f := fun w => funOf w (funOf x (ofNat 2)))
      (g := fun B => funOf B (funOf u (funOf x (ofNat 1))))
      (funOf_isScottContinuous_left (funOf x (ofNat 2)))
      (funOf_isScottContinuous_left (funOf u (funOf x (ofNat 1)))))

end DomainTheory.DataTypesAsLattices
