/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_5
import DomainTheory.DataTypesAsLattices.Lambda.dollarStep_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.eq_2_24_Y


namespace DomainTheory.DataTypesAsLattices











































/-- **Scott 1976, (2.24).** `$ = Y(step)` as a combinator application. -/
theorem eq_2_24_Ycomb : funOf Ycomb (graph dollarStep) = dollarC := by
  rw [theorem_2_5 dollarStep_isScottContinuous, eq_2_24_Y]

end DomainTheory.DataTypesAsLattices
