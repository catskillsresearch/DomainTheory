/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.dollarStepBody_isScottContinuous_u


namespace DomainTheory.DataTypesAsLattices










































theorem dollarStep_app (s u : Pomega) :
    funOf (dollarStep s) u = graph (fun z => dollarStepBody s u z) :=
  beta (graph_const_isScottContinuous (fun u z => dollarStepBody s u z)
    (fun z => dollarStepBody_isScottContinuous_u s z)) u

end DomainTheory.DataTypesAsLattices
