module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_5
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStep_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_24_Y

@[expose] public section


namespace DomainTheory.DataTypesAsLattices











































/-- **Scott 1976, (2.24).** `$ = Y(step)` as a combinator application. -/
theorem eq_2_24_Ycomb : funOf Ycomb (graph dollarStep) = dollarC := by
  rw [theorem_2_5 dollarStep_isScottContinuous, eq_2_24_Y]

end DomainTheory.DataTypesAsLattices
