/-ai
The term unpairDeltaTerm applies variable 2 to variable 0 and then to unpairSquareTerm, the difference between the input and the square of its integer square root in the unpairing environment.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.unpairSquareTerm

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairDeltaTerm : Term :=
  .app (.app (.var 2) (.var 0)) unpairSquareTerm

end DomainTheory.DataTypesAsLattices
