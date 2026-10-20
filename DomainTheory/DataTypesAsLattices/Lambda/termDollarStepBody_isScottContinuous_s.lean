/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left


namespace DomainTheory.DataTypesAsLattices






















































theorem termDollarStepBody_isScottContinuous_s (u z : Pomega) :
    IsScottContinuous (fun s => termDollarStepBody s u z) := by
  have hinner : IsScottContinuous
      (fun s => funOf (funOf s (termShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun s => funOf s (termShift u))
      (funOf_isScottContinuous_left (predSet z))
      (funOf_isScottContinuous_left (termShift u))
  exact theorem_1_3 (condSet_isScottContinuous_right z (funOf u (ofNat 0))) hinner

end DomainTheory.DataTypesAsLattices
