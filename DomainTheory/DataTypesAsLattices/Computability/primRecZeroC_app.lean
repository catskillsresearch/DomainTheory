/-ai
Applying primRecZeroC to a step f yields primRecComb of the numeral 0 and f.

Unfold primRecZeroC and apply the composition law SK_comp twice. The resulting expression is definitionally the primitive-recursion combinator.
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




















theorem primRecZeroC_app (f : Pomega) :
    primRecZeroC ⬝ f = primRecComb (ofNat 0) f := by
  rw [primRecZeroC, SK_comp, SK_comp]
  rfl

end DomainTheory.DataTypesAsLattices
