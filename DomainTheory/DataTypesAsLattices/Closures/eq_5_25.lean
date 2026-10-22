module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.selfArrowStep_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.25).** `d = I ∪ (d ∘→ d)`. -/
theorem eq_5_25 : dEq = Icomb ∪ arrowR dEq dEq :=
  (theorem_1_4 selfArrowStep_isScottContinuous).1.symm

end DomainTheory.DataTypesAsLattices
