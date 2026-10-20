/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.dollarStepBody_isScottContinuous_s


namespace DomainTheory.DataTypesAsLattices










































theorem dollarStep_isScottContinuous : IsScottContinuous dollarStep :=
  graph_const_isScottContinuous
    (fun s u => graph (fun z => dollarStepBody s u z))
    (fun u => graph_const_isScottContinuous
      (fun s z => dollarStepBody s u z)
      (fun z => dollarStepBody_isScottContinuous_s u z))

end DomainTheory.DataTypesAsLattices
