/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.termDollarStepBody_isScottContinuous_z
import DomainTheory.DataTypesAsLattices.Lambda.termDollarStep_app


namespace DomainTheory.DataTypesAsLattices






















































theorem termDollarStep_app2 (s u z : Pomega) :
    funOf (funOf (termDollarStep s) u) z = termDollarStepBody s u z := by
  rw [termDollarStep_app]
  exact beta (termDollarStepBody_isScottContinuous_z s u) z

end DomainTheory.DataTypesAsLattices
