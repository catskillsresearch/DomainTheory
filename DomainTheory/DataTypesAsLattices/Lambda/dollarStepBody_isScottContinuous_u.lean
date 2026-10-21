/-ai
The dollar step body is Scott continuous in the sequence argument.

The else branch composes application to the predecessor with application of the step to the shifted sequence, and the shift is Scott continuous in the sequence. The conditional is Scott continuous in each branch, the left branch is application to the numeral 0, and the right branch is that else branch.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_mid
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.seqShift_left_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem dollarStepBody_isScottContinuous_u (s z : Pomega) :
    IsScottContinuous (fun u => dollarStepBody s u z) := by
  have helse : IsScottContinuous
      (fun u => funOf (funOf s (seqShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun u => funOf s (seqShift u))
      (funOf_isScottContinuous_left (predSet z))
      (theorem_1_3 (funOf_isScottContinuous s) seqShift_left_isScottContinuous)
  exact theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_mid z y)
    (fun x => condSet_isScottContinuous_right z x)
    (funOf_isScottContinuous_left (ofNat 0)) helse

end DomainTheory.DataTypesAsLattices
