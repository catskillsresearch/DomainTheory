/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_mid
import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous


namespace DomainTheory.DataTypesAsLattices

































theorem condC_map_cont :
    IsScottContinuous (fun x => graph (fun y => graph (fun z => condSet z x y))) :=
  graph_const_isScottContinuous
    (fun x y => graph (fun z => condSet z x y))
    (fun y => graph_const_isScottContinuous (fun x z => condSet z x y)
      (fun z => condSet_isScottContinuous_mid z y))

end DomainTheory.DataTypesAsLattices
