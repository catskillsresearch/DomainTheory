/-ai
The second application of the currying combinator, at u and then x, is the graph of y mapped to the application of u to the pair sequence of x and y.

The proof rewrites by the first application rule for the currying combinator, then applies the beta rule to the Scott continuity of the middle currying map at x.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.curry_mid_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.curryC_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















theorem curryC_app2 (u x : Pomega) :
    funOf (funOf curryC u) x = graph (fun y => funOf u (pairSeq x y)) := by
  rw [curryC_app]
  exact beta (curry_mid_isScottContinuous u) x

end DomainTheory.DataTypesAsLattices
