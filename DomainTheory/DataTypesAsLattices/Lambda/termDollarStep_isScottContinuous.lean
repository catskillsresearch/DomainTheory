/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.termDollarStepBody_isScottContinuous_s


namespace DomainTheory.DataTypesAsLattices






















































theorem termDollarStep_isScottContinuous : IsScottContinuous termDollarStep :=
  graph_const_isScottContinuous
    (fun s u => graph (fun z => termDollarStepBody s u z))
    (fun u => graph_const_isScottContinuous
      (fun s z => termDollarStepBody s u z)
      (fun z => termDollarStepBody_isScottContinuous_s u z))

end DomainTheory.DataTypesAsLattices
