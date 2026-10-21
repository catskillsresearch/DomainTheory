/-ai
For fixed s and z, the body of the term-level dollar step is Scott continuous in u.

The else-branch, sending u to the application of the application of s to the term shift of u, evaluated at the predecessor of z, is Scott continuous by two substitutions: left application at the predecessor, and the composite of application of the fixed s with the left continuity of the term shift. Binary substitution then combines continuity of the conditional in its then-branch and in its else-branch with left application at the numeral 0 and with that else-branch.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_mid
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.termShift_left_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem termDollarStepBody_isScottContinuous_u (s z : Pomega) :
    IsScottContinuous (fun u => termDollarStepBody s u z) := by
  have helse : IsScottContinuous
      (fun u => funOf (funOf s (termShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun u => funOf s (termShift u))
      (funOf_isScottContinuous_left (predSet z))
      (theorem_1_3 (funOf_isScottContinuous s) termShift_left_isScottContinuous)
  exact theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_mid z y)
    (fun x => condSet_isScottContinuous_right z x)
    (funOf_isScottContinuous_left (ofNat 0)) helse

end DomainTheory.DataTypesAsLattices
