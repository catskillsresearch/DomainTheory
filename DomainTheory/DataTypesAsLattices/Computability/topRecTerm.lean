/-ai
The term topRecTerm is Scott's equation (2.16), the combinator for the map sending x to the union of the numeral 0 with the successor of x. It abstracts the conditional whose test is an abstraction of the zero term, whose zero branch is zero, and whose successor branch is the successor of the bound variable.
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

/-- **Scott 1976, (2.16).** Combinator for `λx. 0 ∪ (x+1)`. -/
def topRecTerm : Term :=
  .lam 0 (.cond (.lam 1 .zero) .zero (.succ (.var 0)))

end DomainTheory.DataTypesAsLattices
