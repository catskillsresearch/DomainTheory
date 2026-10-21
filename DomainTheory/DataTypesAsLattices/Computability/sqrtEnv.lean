/-ai
The environment sqrtEnv returns the comparison combinator leC at index 3, the multiplication combinator mulC at index 4, and the bottom element at every other index.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.mulC
public import DomainTheory.DataTypesAsLattices.Computability.leC

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def sqrtEnv : ℕ → Pomega
  | 3 => leC
  | 4 => mulC
  | _ => botElem

end DomainTheory.DataTypesAsLattices
