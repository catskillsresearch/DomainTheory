/-ai
The term sqrtStepTerm is the term λn. λ_. λa. if (a + 1) squared is at most n then a + 1 else a. It abstracts variables 0, 1, and 2 from the conditional whose test applies variable 3 to the product, under variable 4, of the two successors of variable 2 and to variable 0, whose zero branch is variable 2, and whose successor branch is the successor of variable 2.
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

/-- `λn _ a. if (a+1)^2 ≤ n then a+1 else a`. -/
def sqrtStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2
    (.cond
      (.app (.app (.var 3)
        (.app (.app (.var 4) (.succ (.var 2))) (.succ (.var 2))))
        (.var 0))
      (.var 2)
      (.succ (.var 2)))))

end DomainTheory.DataTypesAsLattices
