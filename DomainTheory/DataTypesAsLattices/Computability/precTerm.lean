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

/-- On packed input `(z,n)`, recurse from `f z` with
step `λy ih. g (pair z (pair y ih))`. -/
def precTerm : Term :=
  .lam 0
    (.app
      (.app
        (.app (.var 3) (.app (.var 4) (.app (.var 6) (.var 0))))
        (.lam 1 (.lam 2
          (.app (.var 5)
            (.app (.app (.var 8) (.app (.var 6) (.var 0)))
              (.app (.app (.var 8) (.var 1)) (.var 2)))))))
      (.app (.var 7) (.var 0)))

end DomainTheory.DataTypesAsLattices
