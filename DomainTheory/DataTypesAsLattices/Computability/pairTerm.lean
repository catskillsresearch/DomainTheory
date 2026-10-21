/-ai
The pairing term is λa λb. (b − a) ⊃ (a·a + a + b), (b·b + a), with addition, multiplication, and subtraction free.
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

/-- `λa λb. (b-a) ⊃ (a*a+a+b), (b*b+a)` with free `add, mul, sub`. -/
def pairTerm : Term :=
  .lam 3 (.lam 4
    (.cond (.app (.app (.var 2) (.var 4)) (.var 3))
      (.app (.app (.var 0)
          (.app (.app (.var 0)
              (.app (.app (.var 1) (.var 3)) (.var 3)))
            (.var 3)))
        (.var 4))
      (.app (.app (.var 0)
          (.app (.app (.var 1) (.var 4)) (.var 4)))
        (.var 3))))

end DomainTheory.DataTypesAsLattices
