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



















































theorem termShift_left_isScottContinuous : IsScottContinuous termShift :=
  graph_const_isScottContinuous (fun u t => funOf u (succSet t))
    (fun t => funOf_isScottContinuous_left (succSet t))

end DomainTheory.DataTypesAsLattices
