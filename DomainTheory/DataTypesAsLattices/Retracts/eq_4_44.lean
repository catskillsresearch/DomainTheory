module

public import DomainTheory.DataTypesAsLattices.Retracts.expF
public import DomainTheory.DataTypesAsLattices.Retracts.expR
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_5
public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_4
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem eq_4_44 : expR = expF expR := by
  have hY : expR = fix expF := theorem_2_5 expF.isScottContinuous
  have hfix : expF expR = expR := by
    rw [hY]
    exact (theorem_1_4 expF.isScottContinuous).1
  exact hfix.symm

end DomainTheory.DataTypesAsLattices
