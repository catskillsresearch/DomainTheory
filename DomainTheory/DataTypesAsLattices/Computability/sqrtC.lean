module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.primRecZeroC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepC

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- A combinator realizing integer square root. -/
def sqrtC : Pomega :=
  Scomb ⬝
    (Scomb ⬝ (Kcomb ⬝ primRecZeroC) ⬝ sqrtStepC) ⬝
    (Scomb ⬝ Kcomb ⬝ Kcomb)

end DomainTheory.DataTypesAsLattices
