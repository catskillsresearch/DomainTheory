/-ai
If z is distinct from bottom, the conditional set of z with both branches equal to x equals x.

If 0 belongs to z and z is the numeral 0, the zero case of the conditional (2.7) returns x. If 0 belongs to z but z is distinct from the numeral 0, the mixed case returns the union of x with itself, which simplifies to x. If 0 does not belong to z, the remaining case of (2.7) returns the second branch, using that z is distinct from bottom.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem condSet_same (z x : Pomega) (hz : z ≠ botElem) : condSet z x x = x := by
  by_cases h0 : 0 ∈ z
  · by_cases hsing : z = ofNat 0
    · subst hsing
      exact eq_2_7_zero x x
    · rw [eq_2_7_mix x x z h0 hsing]
      simp
  · exact eq_2_7_pos x x z h0 hz

end DomainTheory.DataTypesAsLattices
