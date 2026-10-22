module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.subC
public import DomainTheory.DataTypesAsLattices.Computability.isZeroC

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- `λn λm. isZero (n − m)`. -/
def leC : Pomega :=
  Scomb ⬝ (Kcomb ⬝ (Scomb ⬝ (Kcomb ⬝ isZeroC))) ⬝ subC

end DomainTheory.DataTypesAsLattices
