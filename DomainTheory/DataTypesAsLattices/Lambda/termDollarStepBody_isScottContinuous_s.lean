/-ai
For fixed u and z, the body of the term-level dollar step is Scott continuous in s.

The inner map sending s to the application of the application of s to the term shift of u, evaluated at the predecessor of z, is a composite of two left-application maps, hence Scott continuous by the substitution theorem. The body is the conditional of a value independent of s with that inner map, so a further substitution, using continuity of the conditional in its else-branch, gives continuity in s.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem termDollarStepBody_isScottContinuous_s (u z : Pomega) :
    IsScottContinuous (fun s => termDollarStepBody s u z) := by
  have hinner : IsScottContinuous
      (fun s => funOf (funOf s (termShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun s => funOf s (termShift u))
      (funOf_isScottContinuous_left (predSet z))
      (funOf_isScottContinuous_left (termShift u))
  exact theorem_1_3 (condSet_isScottContinuous_right z (funOf u (ofNat 0))) hinner

end DomainTheory.DataTypesAsLattices
