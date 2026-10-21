/-ai
The term shift, as a map of its argument u, is Scott continuous.

It is the graph of a family that is Scott continuous in u: for each t, left application at the successor of t is Scott continuous.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



















































theorem termShift_left_isScottContinuous : IsScottContinuous termShift :=
  graph_const_isScottContinuous (fun u t => funOf u (succSet t))
    (fun t => funOf_isScottContinuous_left (succSet t))

end DomainTheory.DataTypesAsLattices
