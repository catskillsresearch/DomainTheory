/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_mid


namespace DomainTheory.DataTypesAsLattices









theorem dcondSet_isScottContinuous_mid (z y : Pomega) :
    IsScottContinuous (fun x => dcondSet z x y) :=
  theorem_1_3 (f := fun w => condSet z w (condSet z topElem y))
    (g := fun x => condSet z x topElem)
    (condSet_isScottContinuous_mid z (condSet z topElem y))
    (condSet_isScottContinuous_mid z topElem)

end DomainTheory.DataTypesAsLattices
