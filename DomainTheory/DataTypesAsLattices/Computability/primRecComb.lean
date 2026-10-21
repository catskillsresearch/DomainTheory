/-ai
Scott’s equation (2.27) packaged as a combinator: the dollar combinator applied to the fixed-point combinator Y applied to the interpretation of the primitive-recursion step term at a base a and a step f.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Scott (2.27) packaged as a combinator. -/
def primRecComb (a f : Pomega) : Pomega :=
  funOf dollarC
    (funOf Ycomb
      (funOf (funOf (interp primRecStepTerm (fun _ => botElem)) a) f))

end DomainTheory.DataTypesAsLattices
