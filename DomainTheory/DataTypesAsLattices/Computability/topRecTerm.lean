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

/-- **Scott 1976, (2.16).** Combinator for `λx. 0 ∪ (x+1)`. -/
def topRecTerm : Term :=
  .lam 0 (.cond (.lam 1 .zero) .zero (.succ (.var 0)))

end DomainTheory.DataTypesAsLattices
