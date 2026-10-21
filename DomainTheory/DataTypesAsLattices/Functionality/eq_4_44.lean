/-ai
Scott 1976, (4.44). The expression retract is the least fixed point of the seven-tag syntax functor, hence equals the functor applied to the expression retract.

Theorem 2.5, from Scott continuity of the functor, identifies the expression retract with the fixed point of the functor. Theorem 1.4 says that fixed point is fixed, so the functor returns the expression retract. The reverse of that equality is the claim.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.expF_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, (4.44).** `exp` is the least fixed point of the seven-tag
syntax functor. -/
theorem eq_4_44 : expR = expF expR := by
  have hY : expR = fix expF := theorem_2_5 expF_isScottContinuous
  have hfix : expF expR = expR := by
    rw [hY]
    exact (theorem_1_4 expF_isScottContinuous).1
  exact hfix.symm

end DomainTheory.DataTypesAsLattices
