/-ai
The term unpairSqrtTerm is the application of variable 1 to variable 0, the integer square root of the input in the unpairing environment.
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

def unpairSqrtTerm : Term := .app (.var 1) (.var 0)

end DomainTheory.DataTypesAsLattices
