/-ai
The constant combinator for a natural number k is K applied to the numeral of k.
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

def constComb (k : ℕ) : Pomega := funOf Kcomb (ofNat k)

end DomainTheory.DataTypesAsLattices
