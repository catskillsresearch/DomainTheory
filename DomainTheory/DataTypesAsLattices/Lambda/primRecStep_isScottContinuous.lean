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
import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous


namespace DomainTheory.DataTypesAsLattices















































theorem primRecStep_isScottContinuous (a f : Pomega) :
    IsScottContinuous (primRecStep a f) :=
  graph_const_isScottContinuous
    (fun u n => condSet n a (funOf (funOf f (predSet n)) (funOf u (predSet n))))
    (fun n => theorem_1_3 (condSet_isScottContinuous_right n a)
      (theorem_1_3 (funOf_isScottContinuous (funOf f (predSet n)))
        (funOf_isScottContinuous_left (predSet n))))

end DomainTheory.DataTypesAsLattices
