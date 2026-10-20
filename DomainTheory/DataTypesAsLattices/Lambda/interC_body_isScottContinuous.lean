/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.interC_else_isScottContinuous


namespace DomainTheory.DataTypesAsLattices





































theorem interC_body_isScottContinuous :
    IsScottContinuous (fun x =>
      graph (fun y =>
        condSet x (condSet y (ofNat 0) botElem)
          (succSet (funOf (funOf interC (predSet x)) (predSet y))))) :=
  graph_const_isScottContinuous
    (fun x y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf interC (predSet x)) (predSet y))))
    (fun y =>
      theorem_1_3_tuple
        (fun els => condSet_isScottContinuous_left
          (condSet y (ofNat 0) botElem) els)
        (fun tes => condSet_isScottContinuous_right tes
          (condSet y (ofNat 0) botElem))
        id_isScottContinuous
        (interC_else_isScottContinuous y))

end DomainTheory.DataTypesAsLattices
