/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.predSet_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous


namespace DomainTheory.DataTypesAsLattices










































theorem dollarStepBody_isScottContinuous_z (s u : Pomega) :
    IsScottContinuous (fun z => dollarStepBody s u z) :=
  theorem_1_3_tuple
    (fun y => condSet_isScottContinuous_left (funOf u (ofNat 0)) y)
    (fun z => condSet_isScottContinuous_right z (funOf u (ofNat 0)))
    id_isScottContinuous
    (theorem_1_3 (funOf_isScottContinuous (funOf s (seqShift u)))
      predSet_isScottContinuous)

end DomainTheory.DataTypesAsLattices
