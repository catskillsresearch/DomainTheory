/-ai
Applying the dollar step at s to u yields the graph of z ↦ the body at s, u, and z.

This is the beta law for that graph, using Scott continuity of the body in u.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStepBody_isScottContinuous_u

@[expose] public section


namespace DomainTheory.DataTypesAsLattices










































theorem dollarStep_app (s u : Pomega) :
    funOf (dollarStep s) u = graph (fun z => dollarStepBody s u z) :=
  beta (graph_const_isScottContinuous (fun u z => dollarStepBody s u z)
    (fun z => dollarStepBody_isScottContinuous_u s z)) u

end DomainTheory.DataTypesAsLattices
