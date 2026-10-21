/-ai
The term primRecOpTerm is the lambda term binding variables 0 and 1 whose body applies variable 2 to the application of variable 3 to the application of variable 4 to variable 0 and then to variable 1, the curried body of the primitive-recursion operator.
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

def primRecOpTerm : Term :=
  .lam 0 (.lam 1
    (.app (.var 2)
      (.app (.var 3) (.app (.app (.var 4) (.var 0)) (.var 1)))))

end DomainTheory.DataTypesAsLattices
