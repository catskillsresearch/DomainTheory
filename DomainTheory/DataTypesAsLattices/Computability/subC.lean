/-ai
The element subC packages truncated subtraction as primitive recursion on the constant step subStepC. It is the S combinator applied to K applied to the application combinator, and to S applied to K applied to the fixed-point combinator and to S applied to the interpretation of primRecStepTerm in the constantly bottom environment and to K applied to subStepC.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.subStepC

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def subC : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb (funOf Kcomb Ycomb))
      (funOf (funOf Scomb (interp primRecStepTerm (fun _ => botElem)))
        (funOf Kcomb subStepC)))

end DomainTheory.DataTypesAsLattices
