/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.seqFun_left_isScottContinuous


namespace DomainTheory.DataTypesAsLattices







































theorem dollarC_app (u : Pomega) :
    funOf dollarC u = graph (fun x => seqFun u x) :=
  beta (graph_const_isScottContinuous (fun u x => seqFun u x)
    (fun x => seqFun_left_isScottContinuous x)) u

end DomainTheory.DataTypesAsLattices
