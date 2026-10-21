/-ai
The third application of the currying combinator, at u, x, and y, equals the application of u to the pair sequence of x and y.

The proof rewrites by the second application rule, then applies the beta rule to the Scott continuity of the currying body in y.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.curry_body_isScottContinuous_y
public import DomainTheory.DataTypesAsLattices.Functionality.curryC_app2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















theorem curryC_app3 (u x y : Pomega) :
    funOf (funOf (funOf curryC u) x) y = funOf u (pairSeq x y) := by
  rw [curryC_app2]
  exact beta (curry_body_isScottContinuous_y u x) y

end DomainTheory.DataTypesAsLattices
