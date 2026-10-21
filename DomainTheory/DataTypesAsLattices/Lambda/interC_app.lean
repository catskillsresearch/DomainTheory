/-ai
Applying interC twice yields the conditional that returns zero when both arguments are zero and otherwise the successor of interC applied to the two predecessors.

The outer application is rewritten by the graph equation for interC, and the beta law is applied to continuity of the then-else branch in the second argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.interC_app_graph
public import DomainTheory.DataTypesAsLattices.Lambda.interC_then_else_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





































theorem interC_app (x y : Pomega) :
    funOf (funOf interC x) y =
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf interC (predSet x)) (predSet y))) := by
  rw [interC_app_graph]
  exact beta (interC_then_else_isScottContinuous x) y

end DomainTheory.DataTypesAsLattices
