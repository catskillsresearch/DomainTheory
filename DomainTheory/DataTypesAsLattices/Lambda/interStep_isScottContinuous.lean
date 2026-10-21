/-ai
The step interStep is Scott continuous.

Graph continuity reduces the claim to continuity of the inner graph, and a second use of graph continuity reduces that to continuity of the conditional body. Theorem 1.3 applies continuity of the conditional in its right argument, then continuity of successor, then continuity of application in the function argument at each of the two predecessors.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices




































theorem interStep_isScottContinuous :
    IsScottContinuous interStep := by
  refine graph_const_isScottContinuous
    (fun f x => graph (fun y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf f (predSet x)) (predSet y))))) ?_
  intro x
  refine graph_const_isScottContinuous
    (fun f y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf f (predSet x)) (predSet y)))) ?_
  intro y
  refine theorem_1_3
    (condSet_isScottContinuous_right x (condSet y (ofNat 0) botElem)) ?_
  refine theorem_1_3 succSet_isScottContinuous ?_
  exact theorem_1_3
    (f := fun t => funOf t (predSet y))
    (g := fun f => funOf f (predSet x))
    (funOf_isScottContinuous_left (predSet y))
    (funOf_isScottContinuous_left (predSet x))

end DomainTheory.DataTypesAsLattices
