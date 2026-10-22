/-ai
The term unpairTestTerm applies variable 4 to the successor of unpairDeltaTerm and to unpairSqrtTerm, the comparison of one more than the unpairing remainder with the integer square root.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.unpairSqrtTerm
public import DomainTheory.DataTypesAsLattices.Computability.unpairDeltaTerm

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def unpairTestTerm : Term :=
  .app (.app (.var 4) (.succ unpairDeltaTerm)) unpairSqrtTerm

end DomainTheory.DataTypesAsLattices
