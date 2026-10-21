/-ai
The comparison combinator is λn λm. isZero(n − m). It is written as S applied to K applied to S applied to K applied to the zero test, and then to the subtraction combinator.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.subC
public import DomainTheory.DataTypesAsLattices.Computability.isZeroC

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- `λn λm. isZero (n − m)`. -/
def leC : Pomega :=
  Scomb ⬝ (Kcomb ⬝ (Scomb ⬝ (Kcomb ⬝ isZeroC))) ⬝ subC

end DomainTheory.DataTypesAsLattices
