/-ai
For the nested positive branch of u at the positive branch of v at R of x, application to the numeral 1 returns u, application of the inner branch to the numeral 1 returns v, and application of the inner branch to the numeral 2 returns x.

The first two conjuncts are the projection of a positive branch at the numeral 1. The third rewrites by the projection of a positive branch at the numeral 2, the application law for R, and sequencing at the numeral 1.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.Rcomb_app
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos_one
public import DomainTheory.DataTypesAsLattices.Enumeration.barPos_two

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

















































/-- Projection calculation used in the proof of Scott 1976, (3.17). -/
theorem eq_3_17_projections (u v x : Pomega) :
    funOf (barPos u (barPos v (funOf Rcomb x))) (ofNat 1) = u ∧
      funOf (barPos v (funOf Rcomb x)) (ofNat 1) = v ∧
        funOf (barPos v (funOf Rcomb x)) (ofNat 2) = x := by
  refine ⟨barPos_one _ _, barPos_one _ _, ?_⟩
  rw [barPos_two, Rcomb_app, seq2_app_one]

end DomainTheory.DataTypesAsLattices
