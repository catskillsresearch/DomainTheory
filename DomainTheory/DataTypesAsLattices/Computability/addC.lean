module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.addStepC

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- `λx. primRecComb x (K suc)`. -/
def addC : Pomega :=
  funOf (funOf Scomb (funOf Kcomb dollarC))
    (funOf (funOf Scomb (funOf Kcomb Ycomb))
      (funOf (funOf Scomb (interp primRecStepTerm (fun _ => botElem)))
        (funOf Kcomb addStepC)))

end DomainTheory.DataTypesAsLattices
