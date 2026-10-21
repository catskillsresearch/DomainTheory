/-ai
The bar step term is the closed term that abstracts three variables and conditions on the application of the third variable to zero. The first branch is the positive-branch term. The second branch applies the first variable to the application of the second variable to the application of the third variable to the successor of zero, and then to the application of the third variable to the double successor of zero. It is a closed term for the functional whose least fixed point is the bar combinator.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85
public import DomainTheory.DataTypesAsLattices.Enumeration.barPosTerm

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Closed term for the functional whose least fixed point is `barComb`. -/
def barStepTerm : Term :=
  .lam 0 (.lam 1 (.lam 2
    (.cond (.app (.var 2) .zero) barPosTerm
      (.app
        (.app (.var 0)
          (.app (.var 1) (.app (.var 2) (.succ .zero))))
        (.app (.var 2) (.succ (.succ .zero)))))))

end DomainTheory.DataTypesAsLattices
