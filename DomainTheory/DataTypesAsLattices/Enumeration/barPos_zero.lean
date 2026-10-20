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
