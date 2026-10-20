/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.envR_map_isScottContinuous


namespace DomainTheory.DataTypesAsLattices

































theorem envR_app (t : Pomega) :
    funOf envR t = graph (fun n => funOf lambR (funOf t n)) :=
  beta envR_map_isScottContinuous t

end DomainTheory.DataTypesAsLattices
