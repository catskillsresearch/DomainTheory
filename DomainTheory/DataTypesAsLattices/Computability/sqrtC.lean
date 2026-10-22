/-ai
The element sqrtC is a combinator realizing the integer square root. It is the S combinator applied to S applied to K applied to primRecZeroC and to sqrtStepC, and then applied to S applied to K and to K.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.primRecZeroC
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepC

@[expose] public section

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
