/-ai
Applying the multiplication combinator to x yields the primitive recursion of the numeral 0 at the step K applied to addition applied to x.

Rewrite the definitions of multiplication and of primitive recursion by the composition identity for S and K, four times.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.SK_comp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4













theorem mulC_app (x : Pomega) :
    mulC ⬝ x = primRecComb (ofNat 0) (Kcomb ⬝ (addC ⬝ x)) := by
  rw [mulC, primRecComb, SK_comp, SK_comp, SK_comp, SK_comp]

end DomainTheory.DataTypesAsLattices
