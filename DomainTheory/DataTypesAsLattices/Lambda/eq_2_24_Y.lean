/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.dollarStep_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.dollarStep_app2
import DomainTheory.DataTypesAsLattices.Lambda.dollarStep_fix_app


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
