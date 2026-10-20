module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_app
public import DomainTheory.DataTypesAsLattices.Enumeration.Lcomb_app
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos_one
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos_two

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































/-- **Scott 1976, (3.16).** `L(ū⁺(R(x))) = u(x)` on the zero-test branch. -/
theorem eq_3_16 (u x : Pomega) :
    funOf Lcomb (barPos u (funOf Rcomb x)) = funOf u x := by
  rw [Lcomb_app, barPos_one, barPos_two, Rcomb_app, seq2_app_one]

end DomainTheory.DataTypesAsLattices
