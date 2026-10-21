/-ai
The element primRecZeroC is primitive recursion with initial value zero, viewed as an operator on its step. It is the S combinator applied to K applied to the application combinator dollarC, and to S applied to K applied to the fixed-point combinator Ycomb and to the interpretation of primRecStepTerm in the constantly bottom environment applied to the numeral 0.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Primitive recursion with zero initial value, viewed as an operator on its step. -/
def primRecZeroC : Pomega :=
  Scomb ⬝ (Kcomb ⬝ dollarC) ⬝
    (Scomb ⬝ (Kcomb ⬝ Ycomb) ⬝
      (interp primRecStepTerm (fun _ => botElem) ⬝ ofNat 0))

end DomainTheory.DataTypesAsLattices
