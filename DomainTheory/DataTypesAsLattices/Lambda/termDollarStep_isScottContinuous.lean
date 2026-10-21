/-ai
The term-level dollar step is Scott continuous as a map of s.

It is the graph of a family of graphs. For each u the inner graph is Scott continuous in s because the body is Scott continuous in s for each z, and the outer graph is therefore Scott continuous in s.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStepBody_isScottContinuous_s

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















































theorem termDollarStep_isScottContinuous : IsScottContinuous termDollarStep :=
  graph_const_isScottContinuous
    (fun s u => graph (fun z => termDollarStepBody s u z))
    (fun u => graph_const_isScottContinuous
      (fun s z => termDollarStepBody s u z)
      (fun z => termDollarStepBody_isScottContinuous_s u z))

end DomainTheory.DataTypesAsLattices
