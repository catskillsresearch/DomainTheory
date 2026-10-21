/-ai
The outer map of S, sending u to the graph of the map sending v to the graph of the map sending x to the application of u at x applied to v at x, is Scott continuous.

It is a graph of continuous components. For each v the inner graph is continuous because, for each x, Theorem 1.3 composes left continuity of application at the application of v to x with left continuity of application at x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem Scomb_map_cont :
    IsScottContinuous (fun u => graph (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x)))) :=
  graph_const_isScottContinuous
    (fun u v => graph (fun x => funOf (funOf u x) (funOf v x)))
    (fun v => graph_const_isScottContinuous
      (fun u x => funOf (funOf u x) (funOf v x))
      (fun x => theorem_1_3
        (f := fun t => funOf t (funOf v x))
        (g := fun u => funOf u x)
        (funOf_isScottContinuous_left (funOf v x))
        (funOf_isScottContinuous_left x)))

end DomainTheory.DataTypesAsLattices
