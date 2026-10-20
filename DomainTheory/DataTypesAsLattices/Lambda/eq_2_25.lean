/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.seqFun_right_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.dollarC_app


namespace DomainTheory.DataTypesAsLattices







































/-- **Scott 1976, (2.25).** `$ (u) = λx. ⋃ {u_i | i ∈ x}`. -/
theorem eq_2_25 (u x : Pomega) :
    funOf (funOf dollarC u) x = seqFun u x := by
  rw [dollarC_app]
  exact beta (seqFun_right_isScottContinuous u) x

end DomainTheory.DataTypesAsLattices
