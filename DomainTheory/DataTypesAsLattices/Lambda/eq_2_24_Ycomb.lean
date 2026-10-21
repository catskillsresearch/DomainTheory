/-ai
Scott 1976, (2.24). Y applied to the graph of the dollar step is the dollar combinator.

The fixed-point theorem sends Y of that graph to the least fixed point of the step, and that fixed point is the dollar combinator.
ai-/
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
