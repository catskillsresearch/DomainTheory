/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices

































theorem envR_map_isScottContinuous :
    IsScottContinuous (fun t => graph (fun n => funOf lambR (funOf t n))) :=
  graph_const_isScottContinuous
    (fun t n => funOf lambR (funOf t n))
    (fun n => theorem_1_3 (funOf_isScottContinuous lambR)
      (funOf_isScottContinuous_left n))

end DomainTheory.DataTypesAsLattices
