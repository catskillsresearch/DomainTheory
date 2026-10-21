/-ai
The term unpairSquareTerm applies variable 3 to unpairSqrtTerm and again to unpairSqrtTerm, the square of the integer square root in the unpairing environment.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.unpairSqrtTerm

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairSquareTerm : Term :=
  .app (.app (.var 3) unpairSqrtTerm) unpairSqrtTerm

end DomainTheory.DataTypesAsLattices
