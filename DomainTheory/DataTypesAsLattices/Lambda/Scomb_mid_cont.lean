/-ai
For fixed u, the middle map of S, sending v to the graph of the map sending x to the application of u at x applied to v at x, is Scott continuous.

It is a graph of continuous components. For each x, Theorem 1.3 composes continuity of application of the application of u to x with left continuity of application at x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem Scomb_mid_cont (u : Pomega) :
    IsScottContinuous (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x))) :=
  graph_const_isScottContinuous
    (fun v x => funOf (funOf u x) (funOf v x))
    (fun x => theorem_1_3 (funOf_isScottContinuous (funOf u x))
      (funOf_isScottContinuous_left x))

end DomainTheory.DataTypesAsLattices
