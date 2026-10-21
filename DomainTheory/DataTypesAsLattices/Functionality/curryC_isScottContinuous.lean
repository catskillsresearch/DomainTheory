/-ai
The map sending u to the graph of x mapped to the graph of y mapped to the application of u to the pair sequence of x and y is Scott-continuous.

Constancy of graphs under Scott continuity reduces the claim to continuity, for each x, of the inner graph in u, and that inner graph is continuous by the same principle from left continuity of application at the pair sequence of x and y.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem curryC_isScottContinuous :
    IsScottContinuous (fun u =>
      graph (fun x => graph (fun y => funOf u (pairSeq x y)))) :=
  graph_const_isScottContinuous
    (fun u x => graph (fun y => funOf u (pairSeq x y)))
    (fun x =>
      graph_const_isScottContinuous
        (fun u y => funOf u (pairSeq x y))
        (fun y => funOf_isScottContinuous_left (pairSeq x y)))

end DomainTheory.DataTypesAsLattices
