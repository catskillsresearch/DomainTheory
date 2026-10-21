/-ai
Applying the bar combinator to u and then to R applied to x yields the positive bar branch of u at R applied to x.

Rewrite by the two-argument application of the bar combinator and unfold the bar step body. Applying R to x and then to the numeral 0 yields the numeral 0, so the zero case of the conditional (2.7) selects the first branch.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb_app2
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_app_zero

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


















































theorem barComb_on_R (u x : Pomega) :
    funOf (funOf barComb u) (funOf Rcomb x) =
      barPos u (funOf Rcomb x) := by
  rw [barComb_app2, barStepBody, Rcomb_app_zero, eq_2_7_zero]

end DomainTheory.DataTypesAsLattices
