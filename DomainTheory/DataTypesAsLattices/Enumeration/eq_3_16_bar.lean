/-ai
Scott 1976, (3.16): applying L to the result of applying the bar combinator of u to R of x yields the application of u to x.

Rewrite by the two-argument application of the bar combinator, unfold the bar step body, and use that R applied to x and then to the numeral 0 is the numeral 0, so the zero case of the conditional (2.7) selects the first branch. Equation (3.16) then gives the application of u to x.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb_app2
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_app_zero
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_16

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


/-- **Scott 1976, (3.16).** `L ∘ ū ∘ R = λx. u(x)` from the Y-definition. -/
theorem eq_3_16_bar (u x : Pomega) :
    funOf Lcomb (funOf (funOf barComb u) (funOf Rcomb x)) = funOf u x := by
  rw [barComb_app2, barStepBody, Rcomb_app_zero, eq_2_7_zero]
  exact eq_3_16 u x

end DomainTheory.DataTypesAsLattices
