/-ai
For fixed u, the map sending x to the graph of y mapped to the application of u to the pair sequence of x and y is Scott-continuous.

Constancy of graphs under Scott continuity applies, using for each y Theorem 1.3 of continuity of application of u and left continuity of the pair sequence at y.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_left

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















theorem curry_mid_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun x => graph (fun y => funOf u (pairSeq x y))) :=
  graph_const_isScottContinuous
    (fun x y => funOf u (pairSeq x y))
    (fun y => theorem_1_3 (funOf_isScottContinuous u)
      (pairSeq_isScottContinuous_left y))

end DomainTheory.DataTypesAsLattices
