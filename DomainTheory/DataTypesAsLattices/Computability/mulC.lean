/-ai
The multiplication combinator is λx. primRec(0, K (add x)). It is written by applying S, K, the dollar combinator, the fixed-point combinator Y, the interpretation of the primitive-recursion step term, the numeral 0, and the addition combinator.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.addC

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- `λx. primRecComb 0 (K (addC x))`. -/
def mulC : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb (funOf Kcomb Ycomb))
      (funOf (funOf Scomb
          (funOf Kcomb
            (funOf (interp primRecStepTerm (fun _ => botElem)) (ofNat 0))))
        (funOf (funOf Scomb (funOf Kcomb Kcomb)) addC)))

end DomainTheory.DataTypesAsLattices
