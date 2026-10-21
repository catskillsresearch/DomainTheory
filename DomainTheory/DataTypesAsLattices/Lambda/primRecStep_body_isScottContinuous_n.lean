/-ai
With the base, the step, and the functional fixed, the body of the primitive-recursion step is Scott continuous in the argument.

The tuple form of Theorem 1.3 uses continuity of the conditional in its left and right arguments and continuity of the identity. The else branch is a second tuple form, using continuity of application in each argument and Theorem 1.3 applied to continuity of application at the step and at the functional, each composed with continuity of the predecessor.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem primRecStep_body_isScottContinuous_n (a f u : Pomega) :
    IsScottContinuous (fun n =>
      condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n)))) :=
  theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_left a y)
    (fun n => condSet_isScottContinuous_right n a)
    id_isScottContinuous
    (theorem_1_3_tuple
      (fun y => funOf_isScottContinuous_left y)
      (fun x => funOf_isScottContinuous x)
      (theorem_1_3 (funOf_isScottContinuous f) predSet_isScottContinuous)
      (theorem_1_3 (funOf_isScottContinuous u) predSet_isScottContinuous))

end DomainTheory.DataTypesAsLattices
