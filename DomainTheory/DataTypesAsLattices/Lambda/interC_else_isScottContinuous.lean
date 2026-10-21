/-ai
For a fixed second argument, the successor of interC applied to the predecessor of the first argument and the predecessor of the second is Scott continuous in the first argument.

Theorem 1.3 composes continuity of successor with application. A second use composes continuity of application in the function argument with application of interC, and that application is Theorem 1.3 applied to continuity of application at interC and continuity of the predecessor.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





































theorem interC_else_isScottContinuous (y : Pomega) :
    IsScottContinuous (fun x =>
      succSet (funOf (funOf interC (predSet x)) (predSet y))) := by
  refine theorem_1_3 (f := succSet) (g := fun x =>
      funOf (funOf interC (predSet x)) (predSet y))
    succSet_isScottContinuous ?_
  refine theorem_1_3
    (f := fun t => funOf t (predSet y))
    (g := fun x => funOf interC (predSet x))
    (funOf_isScottContinuous_left (predSet y)) ?_
  exact theorem_1_3 (funOf_isScottContinuous interC) predSet_isScottContinuous

end DomainTheory.DataTypesAsLattices
