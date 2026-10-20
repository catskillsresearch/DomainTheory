/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_mid
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous


namespace DomainTheory.DataTypesAsLattices









theorem dcondSet_isScottContinuous_left (x y : Pomega) :
    IsScottContinuous (fun z => dcondSet z x y) :=
  theorem_1_3_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    id_isScottContinuous
    (condSet_isScottContinuous_left x topElem)
    (condSet_isScottContinuous_left topElem y)

end DomainTheory.DataTypesAsLattices
