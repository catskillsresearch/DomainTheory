/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.interC_unfold
import DomainTheory.DataTypesAsLattices.Lambda.interC_body_isScottContinuous


namespace DomainTheory.DataTypesAsLattices





































theorem interC_app_graph (x : Pomega) :
    funOf interC x =
      graph (fun y =>
        condSet x (condSet y (ofNat 0) botElem)
          (succSet (funOf (funOf interC (predSet x)) (predSet y)))) := by
  nth_rw 1 [interC_unfold]
  exact beta interC_body_isScottContinuous x

end DomainTheory.DataTypesAsLattices
