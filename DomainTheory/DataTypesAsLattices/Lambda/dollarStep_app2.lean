/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.dollarStepBody_isScottContinuous_z
import DomainTheory.DataTypesAsLattices.Lambda.dollarStep_app


namespace DomainTheory.DataTypesAsLattices










































theorem dollarStep_app2 (s u z : Pomega) :
    funOf (funOf (dollarStep s) u) z = dollarStepBody s u z := by
  rw [dollarStep_app]
  exact beta (dollarStepBody_isScottContinuous_z s u) z

end DomainTheory.DataTypesAsLattices
