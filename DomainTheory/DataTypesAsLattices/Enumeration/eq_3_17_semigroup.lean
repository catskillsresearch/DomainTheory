/-ai
The nested positive branch of u at the positive branch of v at R of x, applied to the numeral 1, equals u, and applying L to the positive branch of the application of u to v at R of x recovers the application of that composite to x.

The first conjunct is the first projection in the calculation for (3.17). The second conjunct is equation (3.16) at the application of u to v.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_16
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_17_projections

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






















































/-- Nested positive-branch packaging of (3.17): `ū⁺(v̄⁺(R(x)))`
has first projection `u` and recovers `u(v)(x)` via `L` after
replacing the head by `u(v)`. -/
theorem eq_3_17_semigroup (u v x : Pomega) :
    funOf (barPos u (barPos v (funOf Rcomb x))) (ofNat 1) = u ∧
      funOf Lcomb (barPos (funOf u v) (funOf Rcomb x)) =
        funOf (funOf u v) x :=
  ⟨(eq_3_17_projections u v x).1, eq_3_16 (funOf u v) x⟩

end DomainTheory.DataTypesAsLattices
