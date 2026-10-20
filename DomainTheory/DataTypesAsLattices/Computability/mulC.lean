module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.addC

@[expose] public section

set_option linter.unusedSectionVars false

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
