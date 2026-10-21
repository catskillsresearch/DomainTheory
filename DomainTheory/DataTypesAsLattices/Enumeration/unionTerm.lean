/-ai
A closed term for binary union is the abstraction, in binders 0 and 1, of the conditional of the constant-zero abstraction between the first variable and the second. Keeping this term explicit avoids making the finite-set code choose a fresh code separately for every finite set.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- A closed term for binary union.  Keeping this term explicit avoids making
`fin` choose a fresh code separately for every finite set. -/
def unionTerm : Term :=
  .lam 0 (.lam 1 (.cond (.lam 2 .zero) (.var 0) (.var 1)))

end DomainTheory.DataTypesAsLattices
