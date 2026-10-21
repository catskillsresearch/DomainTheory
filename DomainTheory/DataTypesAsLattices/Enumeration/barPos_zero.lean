/-ai
Applying the positive bar branch of u and x to the numeral 0 yields the numeral 1.

Simplify by the definition of the positive branch, equation (2.22), and the zero case of the conditional (2.7).
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


theorem barPos_zero (u x : Pomega) :
    funOf (barPos u x) (ofNat 0) = ofNat 1 := by
  simp [barPos, eq_2_22, eq_2_7_zero]

end DomainTheory.DataTypesAsLattices
