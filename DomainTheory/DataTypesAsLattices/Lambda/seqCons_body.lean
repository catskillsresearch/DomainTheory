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



































theorem seqCons_body (x xs : Pomega) :
    IsScottContinuous (fun z => condSet z x (funOf xs (predSet z))) :=
  theorem_1_3_tuple
    (fun _ => condSet_isScottContinuous_left x _)
    (fun z => condSet_isScottContinuous_right z x)
    id_isScottContinuous
    (theorem_1_3 (funOf_isScottContinuous xs) predSet_isScottContinuous)

end DomainTheory.DataTypesAsLattices
