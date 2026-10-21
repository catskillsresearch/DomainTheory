/-ai
Scott 1976, (2.24). The dollar combinator is combinatory: it is Y applied to λs λu λz. z ⊃ u(0), s(λt. u(t + 1))(z − 1).

Y applied to the interpretation of that term in the bottom environment equals the dollar combinator, by the interpretation equation, the fixed-point theorem for the continuous functional of the term, and the identification of the dollar combinator with that fixed point. Y is combinatory and the term is closed, so the application is combinatory.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_5
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4_closed
public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb_combinatory
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.dollarC_eq_fix_termDollarStep
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStepTerm_interp

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















































/-- **Scott 1976, (2.24).** `$` is combinatory: `$ = Y(λs λu λz. z ⊃ u₀, s(λt. u_{t+1})(z−1))`. -/
theorem dollarC_combinatory : IsCombinatory dollarC := by
  have hY : funOf Ycomb (interp dollarStepTerm (fun _ => botElem)) = dollarC := by
    rw [dollarStepTerm_interp, theorem_2_5 termDollarStep_isScottContinuous,
      dollarC_eq_fix_termDollarStep]
  exact hY ▸ IsCombinatory.app Ycomb_combinatory (theorem_2_4_closed dollarStepTerm)

end DomainTheory.DataTypesAsLattices
