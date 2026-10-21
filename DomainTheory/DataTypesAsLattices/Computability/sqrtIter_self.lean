/-ai
Running the square-root iteration for n steps on n yields the integer square root of n.

Rewrite by sqrtIter_eq_min. The minimum of n and the square root is the square root, because Nat.sqrt_le_self says that the square root is at most n.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.sqrtIter_eq_min

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4





















theorem sqrtIter_self (n : ℕ) : sqrtIter n n = Nat.sqrt n := by
  rw [sqrtIter_eq_min, min_eq_right (Nat.sqrt_le_self n)]

end DomainTheory.DataTypesAsLattices
