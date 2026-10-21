/-ai
The dollar step is Scott continuous.

It is the graph of a graph of the body. The body is Scott continuous in the step, so the inner graph is Scott continuous in the step, and therefore the outer graph is as well.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStepBody_isScottContinuous_s

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem dollarStep_isScottContinuous : IsScottContinuous dollarStep :=
  graph_const_isScottContinuous
    (fun s u => graph (fun z => dollarStepBody s u z))
    (fun u => graph_const_isScottContinuous
      (fun s z => dollarStepBody s u z)
      (fun z => dollarStepBody_isScottContinuous_s u z))

end DomainTheory.DataTypesAsLattices
