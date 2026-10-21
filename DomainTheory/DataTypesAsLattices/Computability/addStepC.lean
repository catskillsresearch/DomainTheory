/-ai
The successor step used by the addition combinator is K applied to the successor combinator.
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

def addStepC : Pomega := funOf Kcomb sucC

end DomainTheory.DataTypesAsLattices
