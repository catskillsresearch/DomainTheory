/-ai
The zero test is the conditional combinator applied to the numeral 1 and then to the numeral 0. On the numeral 0 it returns 1, and on a positive numeral it returns 0.
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

/-- `cond 1 0 n` is `1` on `0` and `0` on positive numerals. -/
def isZeroC : Pomega := funOf (funOf condC (ofNat 1)) (ofNat 0)

end DomainTheory.DataTypesAsLattices
