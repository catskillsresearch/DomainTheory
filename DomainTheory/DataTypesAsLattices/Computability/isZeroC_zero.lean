/-ai
The zero test applied to the numeral of 0 yields the numeral of 1.

Unfold the test and rewrite by the three-argument β-rule for the conditional and the zero clause of equation (2.7).
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


theorem isZeroC_zero : funOf isZeroC (ofNat 0) = ofNat 1 := by
  simp only [isZeroC]
  rw [condC_beta3, eq_2_7_zero]

end DomainTheory.DataTypesAsLattices
