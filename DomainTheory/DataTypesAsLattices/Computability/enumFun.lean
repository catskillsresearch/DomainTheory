/-ai
The stage-bounded enumerator of a partial-recursive code c at a stage t returns one more than the first component of the unpairing of t when the bounded evaluation of c at that input, for the number of steps given by the second component, is defined, and returns 0 otherwise.
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

/-- Stage-bounded enumerator associated to a partial-recursive code. -/
def enumFun (c : Code) (t : ℕ) : ℕ :=
  bif (evaln t.unpair.2 c t.unpair.1).isSome
    then t.unpair.1 + 1
    else 0

end DomainTheory.DataTypesAsLattices
