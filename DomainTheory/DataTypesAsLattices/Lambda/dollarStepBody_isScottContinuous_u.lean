/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_mid
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
import DomainTheory.DataTypesAsLattices.Lambda.seqShift_left_isScottContinuous


namespace DomainTheory.DataTypesAsLattices










































theorem dollarStepBody_isScottContinuous_u (s z : Pomega) :
    IsScottContinuous (fun u => dollarStepBody s u z) := by
  have helse : IsScottContinuous
      (fun u => funOf (funOf s (seqShift u)) (predSet z)) :=
    theorem_1_3 (f := fun w => funOf w (predSet z))
      (g := fun u => funOf s (seqShift u))
      (funOf_isScottContinuous_left (predSet z))
      (theorem_1_3 (funOf_isScottContinuous s) seqShift_left_isScottContinuous)
  exact theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_mid z y)
    (fun x => condSet_isScottContinuous_right z x)
    (funOf_isScottContinuous_left (ofNat 0)) helse

end DomainTheory.DataTypesAsLattices
