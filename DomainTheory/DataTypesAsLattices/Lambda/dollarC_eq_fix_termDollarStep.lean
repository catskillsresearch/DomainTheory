/-ai
The dollar combinator is the least fixed point of the functional defined by the dollar step term.

That functional fixes its least fixed point. At the fixed point the body equals sequence revaluation, because two applications of the functional unfold to two applications of the fixed point, which equal the revaluation. The functional at the fixed point is therefore the nested graph of the revaluation, and the fixed-point equation identifies that graph with the fixed point.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep_app2
public import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep_fix_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















































theorem dollarC_eq_fix_termDollarStep : dollarC = fix termDollarStep := by
  have hfix : termDollarStep (fix termDollarStep) = fix termDollarStep :=
    (theorem_1_4 termDollarStep_isScottContinuous).1
  have hbody : ∀ u z, termDollarStepBody (fix termDollarStep) u z = seqFun u z := by
    intro u z
    calc termDollarStepBody (fix termDollarStep) u z
        = funOf (funOf (termDollarStep (fix termDollarStep)) u) z :=
          (termDollarStep_app2 _ _ _).symm
      _ = funOf (funOf (fix termDollarStep) u) z := by rw [hfix]
      _ = seqFun u z := termDollarStep_fix_app u z
  have : termDollarStep (fix termDollarStep) =
      graph (fun u => graph (fun z => seqFun u z)) := by
    apply congrArg graph
    funext u
    apply congrArg graph
    funext z
    exact hbody u z
  exact this.symm.trans hfix

end DomainTheory.DataTypesAsLattices
