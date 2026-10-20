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

/-- `cond 1 0 n` is `1` on `0` and `0` on positive numerals. -/
def isZeroC : Pomega := funOf (funOf condC (ofNat 1)) (ofNat 0)

end DomainTheory.DataTypesAsLattices
