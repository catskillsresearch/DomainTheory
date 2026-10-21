/-ai
The term interStepTerm is a closed term for the body of binary intersection. It abstracts three variables. The conditional on the second variable returns, on its zero branch, the conditional of the third variable between zero and the self-application of ω, where ω is the term λv. v v, and on its positive branch the successor of the recursive application of the first variable to the predecessors of the second and third variables.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- A closed LAMBDA term for the body defining binary intersection. -/
def interStepTerm : Term :=
  let omega : Term := .lam 4 (.app (.var 4) (.var 4))
  .lam 0 (.lam 1 (.lam 2
    (.cond (.var 1)
      (.cond (.var 2) .zero (.app omega omega))
      (.succ (.app (.app (.var 0) (.pred (.var 1))) (.pred (.var 2)))))))

end DomainTheory.DataTypesAsLattices
