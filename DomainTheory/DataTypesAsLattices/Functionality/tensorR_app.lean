/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.tensorR_map_isScottContinuous


namespace DomainTheory.DataTypesAsLattices















theorem tensorR_app (a b u : Pomega) :
    funOf (tensorR a b) u =
      pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))) :=
  beta (tensorR_map_isScottContinuous a b) u

end DomainTheory.DataTypesAsLattices
