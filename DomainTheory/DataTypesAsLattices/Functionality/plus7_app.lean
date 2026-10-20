/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.plus7_map_isScottContinuous


namespace DomainTheory.DataTypesAsLattices
































theorem plus7_app (a0 a1 a2 a3 a4 a5 a6 u : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) u =
      plus7Body a0 a1 a2 a3 a4 a5 a6 u :=
  beta (plus7_map_isScottContinuous a0 a1 a2 a3 a4 a5 a6) u

end DomainTheory.DataTypesAsLattices
