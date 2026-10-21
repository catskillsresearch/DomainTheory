/-ai
With the base and the step fixed, the primitive-recursion step is Scott continuous in the functional argument.

Graph continuity reduces the claim to continuity of the conditional body. For each argument, Theorem 1.3 composes continuity of the conditional in its right argument with continuity of application at the step applied to the predecessor, and that application is continuous in the functional argument by continuity of application in the function argument.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















































theorem primRecStep_isScottContinuous (a f : Pomega) :
    IsScottContinuous (primRecStep a f) :=
  graph_const_isScottContinuous
    (fun u n => condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))))
    (fun n => theorem_1_3 (condSet_isScottContinuous_right n a)
      (theorem_1_3 (funOf_isScottContinuous (funOf f (predSet n)))
        (funOf_isScottContinuous_left (predSet n))))

end DomainTheory.DataTypesAsLattices
