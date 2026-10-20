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

































theorem Scomb_mid_cont (u : Pomega) :
    IsScottContinuous (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x))) :=
  graph_const_isScottContinuous
    (fun v x => funOf (funOf u x) (funOf v x))
    (fun x => theorem_1_3 (funOf_isScottContinuous (funOf u x))
      (funOf_isScottContinuous_left x))

end DomainTheory.DataTypesAsLattices
