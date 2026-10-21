/-ai
Application of the currying combinator at u is the graph of x mapped to the graph of y mapped to the application of u to the pair sequence of x and y.

This is the beta rule for the Scott continuity of the currying combinator, evaluated at u.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.curryC_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem curryC_app (u : Pomega) :
    funOf curryC u = graph (fun x => graph (fun y => funOf u (pairSeq x y))) :=
  beta curryC_isScottContinuous u

end DomainTheory.DataTypesAsLattices
