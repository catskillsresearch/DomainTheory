/-ai
The dollar step body is Scott continuous in the step argument.

The else branch composes application to the predecessor with application to the shifted sequence, so it is Scott continuous in the step. The conditional is Scott continuous in its right argument, and the left branch does not depend on the step.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left

@[expose] public section


namespace DomainTheory.DataTypesAsLattices










































theorem dollarStepBody_isScottContinuous_s (u z : Pomega) :
    IsScottContinuous (fun s => dollarStepBody s u z) := by
  have hinner : IsScottContinuous
      (fun s => funOf (funOf s (seqShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun s => funOf s (seqShift u))
      (funOf_isScottContinuous_left (predSet z))
      (funOf_isScottContinuous_left (seqShift u))
  exact theorem_1_3 (condSet_isScottContinuous_right z (funOf u (ofNat 0))) hinner

end DomainTheory.DataTypesAsLattices
