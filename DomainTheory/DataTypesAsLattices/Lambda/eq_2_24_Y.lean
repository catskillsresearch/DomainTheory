/-ai
Scott 1976, (2.24). The dollar combinator is the least fixed point of the dollar step.

The step fixes its least fixed point. At that fixed point the body equals sequence revaluation, because two applications of the step unfold to two applications of the fixed point, which equal the revaluation. The step at the fixed point is therefore the nested graph that defines the dollar combinator, and the fixed-point equation identifies the two.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStep_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStep_app2
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStep_fix_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (2.24).** `$ = Y(λs λu λz. z ⊃ u₀, s(λt. u_{t+1})(z−1))`. -/
theorem eq_2_24_Y : dollarC = fix dollarStep := by
  have hfix : dollarStep (fix dollarStep) = fix dollarStep :=
    (theorem_1_4 dollarStep_isScottContinuous).1
  have hbody : ∀ u z, dollarStepBody (fix dollarStep) u z = seqFun u z := by
    intro u z
    calc dollarStepBody (fix dollarStep) u z
        = funOf (funOf (dollarStep (fix dollarStep)) u) z :=
          (dollarStep_app2 _ _ _).symm
      _ = funOf (funOf (fix dollarStep) u) z := by rw [hfix]
      _ = seqFun u z := dollarStep_fix_app u z
  have : dollarStep (fix dollarStep) =
      graph (fun u => graph (fun z => seqFun u z)) := by
    apply congrArg graph
    funext u
    apply congrArg graph
    funext z
    exact hbody u z
  exact this.symm.trans hfix

end DomainTheory.DataTypesAsLattices
