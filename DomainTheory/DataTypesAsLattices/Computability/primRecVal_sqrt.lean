/-ai
Primitive recursion from the numeral 0 with step sqrtStepC applied to the numeral n, run for k steps, equals the numeral sqrtIter n k.

The case k = 0 is reflexivity. For a successor, the recursive clause of primRecVal is rewritten as the double application of that step at the numeral k to the value at k. The inductive hypothesis and sqrtStepC_app finish the equality.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepC_app

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

























theorem primRecVal_sqrt (n : ℕ) : ∀ k,
    primRecVal (ofNat 0) (sqrtStepC ⬝ ofNat n) k = ofNat (sqrtIter n k)
  | 0 => rfl
  | k + 1 => by
      rw [show primRecVal (ofNat 0) (sqrtStepC ⬝ ofNat n) (k + 1) =
        ((sqrtStepC ⬝ ofNat n) ⬝ ofNat k) ⬝
          primRecVal (ofNat 0) (sqrtStepC ⬝ ofNat n) k by rfl,
        primRecVal_sqrt n k, sqrtStepC_app]
      rfl

end DomainTheory.DataTypesAsLattices
