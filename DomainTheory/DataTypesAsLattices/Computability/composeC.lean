/-ai
The composition of elements u and v of Pω is the combinator S applied to K applied to u, and then to v.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def composeC (u v : Pomega) : Pomega :=
  funOf (funOf Scomb (funOf Kcomb u)) v

end DomainTheory.DataTypesAsLattices
