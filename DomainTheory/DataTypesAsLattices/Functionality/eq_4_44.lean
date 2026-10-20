/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.expF_isScottContinuous


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
