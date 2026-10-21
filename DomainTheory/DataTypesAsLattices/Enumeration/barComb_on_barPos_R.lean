/-ai
Applying the bar combinator to u and then to the positive branch of v at R applied to x equals applying the bar combinator to the application of u to v, and then to x.

Rewrite by the two-argument application of the bar combinator and unfold the bar step body. The positive branch applied to the numeral 0 is the numeral 1, so the successor case of the conditional (2.7) selects the second branch. The projections of the positive branch at the numerals 1 and 2, the application law for R, and sequencing at the numeral 1 then match the two sides.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_app
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos_zero
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos_one
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos_two
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb_app2

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


















































theorem barComb_on_barPos_R (u v x : Pomega) :
    funOf (funOf barComb u) (barPos v (funOf Rcomb x)) =
      funOf (funOf barComb (funOf u v)) x := by
  rw [barComb_app2, barStepBody, barPos_zero, eq_2_7_succ,
    barPos_one, barPos_two, Rcomb_app, seq2_app_one]

end DomainTheory.DataTypesAsLattices
