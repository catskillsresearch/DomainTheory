/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.succSet_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.predSet_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_mid
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right


namespace DomainTheory.DataTypesAsLattices





































theorem interC_then_else_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf interC (predSet x)) (predSet y)))) :=
  theorem_1_3_tuple
    (fun els => condSet_isScottContinuous_mid x els)
    (fun th => condSet_isScottContinuous_right x th)
    (condSet_isScottContinuous_left (ofNat 0) botElem)
    (theorem_1_3 succSet_isScottContinuous
      (theorem_1_3 (funOf_isScottContinuous (funOf interC (predSet x)))
        predSet_isScottContinuous))

end DomainTheory.DataTypesAsLattices
