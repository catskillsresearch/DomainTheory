module

public import Mathlib.Computability.RE
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
