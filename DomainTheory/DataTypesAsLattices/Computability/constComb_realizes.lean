/-ai
The constant combinator for k realizes the function with constant value k.

Simplify by the definition and the β-rule for K.
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


theorem constComb_realizes (k : ℕ) : Realizes (constComb k) fun _ => k := fun _ => by
  simp [constComb, Kcomb_beta2]

end DomainTheory.DataTypesAsLattices
