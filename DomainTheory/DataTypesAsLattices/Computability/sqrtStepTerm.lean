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
