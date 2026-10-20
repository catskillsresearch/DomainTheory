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
import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left


namespace DomainTheory.DataTypesAsLattices





































theorem interC_else_isScottContinuous (y : Pomega) :
    IsScottContinuous (fun x =>
      succSet (funOf (funOf interC (predSet x)) (predSet y))) := by
  refine theorem_1_3 (f := succSet) (g := fun x =>
      funOf (funOf interC (predSet x)) (predSet y))
    succSet_isScottContinuous ?_
  refine theorem_1_3
    (f := fun t => funOf t (predSet y))
    (g := fun x => funOf interC (predSet x))
    (funOf_isScottContinuous_left (predSet y)) ?_
  exact theorem_1_3 (funOf_isScottContinuous interC) predSet_isScottContinuous

end DomainTheory.DataTypesAsLattices
