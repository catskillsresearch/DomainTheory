/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous


namespace DomainTheory.DataTypesAsLattices























theorem omegaComb_isScottContinuous : IsScottContinuous omegaComb :=
  graph_const_isScottContinuous
    (fun u x => funOf u (funOf x x))
    (fun x => funOf_isScottContinuous_left (funOf x x))

end DomainTheory.DataTypesAsLattices
