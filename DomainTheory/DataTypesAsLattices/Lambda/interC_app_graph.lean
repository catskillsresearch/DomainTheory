/-ai
The application of interC to an argument is the graph of the conditional that returns zero on a zero second argument and otherwise the successor of interC at the two predecessors.

The fixed-point equation unfolds interC, and the beta law is applied to continuity of the body in the first argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.interC_unfold
public import DomainTheory.DataTypesAsLattices.Lambda.interC_body_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





































theorem interC_app_graph (x : Pomega) :
    funOf interC x =
      graph (fun y =>
        condSet x (condSet y (ofNat 0) botElem)
          (succSet (funOf (funOf interC (predSet x)) (predSet y)))) := by
  nth_rw 1 [interC_unfold]
  exact beta interC_body_isScottContinuous x

end DomainTheory.DataTypesAsLattices
