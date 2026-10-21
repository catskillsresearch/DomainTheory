/-ai
The closed term for the functional whose least fixed point is vaal is the double abstraction whose body is the conditional of the application of the inner variable to zero, with zero branch the closed term for G and positive branch the application of the outer variable at the left child of the inner variable to its application at the right child.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85
public import DomainTheory.DataTypesAsLattices.Enumeration.gClosed

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

/-- Closed term for the functional whose least fixed point is `vaal`. -/
def vaalStepTerm : Term :=
  .lam 0 (.lam 1
    (.cond (.app (.var 1) .zero) gClosed
      (.app
        (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) .zero))
        (.app (.var 0) (.app (.app (.var 1) (.succ .zero)) (.succ .zero))))))

end DomainTheory.DataTypesAsLattices
