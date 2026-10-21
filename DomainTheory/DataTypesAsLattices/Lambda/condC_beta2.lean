/-ai
A second application of the conditional combinator, at y, is the graph of the map sending z to the conditional of z, x, and y.

Rewrite by the first beta law, then beta-reduce. The graph is Scott continuous in y because, for each z, the conditional is Scott continuous in its right argument.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.condC_beta

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem condC_beta2 (x y : Pomega) :
    funOf (funOf condC x) y = graph (fun z => condSet z x y) := by
  rw [condC_beta]
  exact beta (graph_const_isScottContinuous (fun y z => condSet z x y)
    (fun z => condSet_isScottContinuous_right z x)) y

end DomainTheory.DataTypesAsLattices
