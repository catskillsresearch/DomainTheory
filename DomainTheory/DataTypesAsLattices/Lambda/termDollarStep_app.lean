/-ai
Applying the term-level dollar step at s to u equals the graph of the body at s and u.

This is the β-law for the graph of a family that is Scott continuous in u, which follows because the body is Scott continuous in u.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStepBody_isScottContinuous_u

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem termDollarStep_app (s u : Pomega) :
    funOf (termDollarStep s) u = graph (fun z => termDollarStepBody s u z) :=
  beta (graph_const_isScottContinuous (fun u z => termDollarStepBody s u z)
    (fun z => termDollarStepBody_isScottContinuous_u s z)) u

end DomainTheory.DataTypesAsLattices
