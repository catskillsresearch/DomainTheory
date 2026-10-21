/-ai
For elements u, v, and x, L applied to G-bar(u) applied to R(x) equals u applied to x; the bar-position of v at R(x), applied to the numeral 1, equals v; and the same bar-position applied to the numeral 2 equals x. These are the pointwise calculations used by Theorem 3.7.

The first equation is the bar form of equation 3.16. The two projection equations are the second and third clauses of equation 3.17.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_16_bar
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_17_projections

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































/-- The pointwise calculations used by Theorem 3.7. -/
theorem theorem_3_7_equations (u v x : Pomega) :
    funOf Lcomb (funOf (funOf barComb u) (funOf Rcomb x)) = funOf u x ∧
      funOf (barPos v (funOf Rcomb x)) (ofNat 1) = v ∧
        funOf (barPos v (funOf Rcomb x)) (ofNat 2) = x :=
  ⟨eq_3_16_bar u x, (eq_3_17_projections u v x).2.1,
    (eq_3_17_projections u v x).2.2⟩

end DomainTheory.DataTypesAsLattices
