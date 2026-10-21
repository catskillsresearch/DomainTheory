/-ai
The closed successor term is the abstraction, in binder 4, of the successor of its bound variable. It is a closed term for one of the five packed combinators of G, and its binder avoids slot 8 so that the term can be placed inside the binary sequence constructor.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Closed terms for the five packed combinators of `G`. Binders avoid
slot 8 so they can be placed inside `seq2Term`. -/
def sucClosed : Term := .lam 4 (.succ (.var 4))

end DomainTheory.DataTypesAsLattices
