/-ai
Applying the dollar combinator to a sequence u yields the graph of x ↦ seq(u)(x).

This is the beta law for that graph, using Scott continuity of sequence revaluation in the sequence.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun_left_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem dollarC_app (u : Pomega) :
    funOf dollarC u = graph (fun x => seqFun u x) :=
  beta (graph_const_isScottContinuous (fun u x => seqFun u x)
    (fun x => seqFun_left_isScottContinuous x)) u

end DomainTheory.DataTypesAsLattices
