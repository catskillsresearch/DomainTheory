/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.diagApp_isScottContinuous


namespace DomainTheory.DataTypesAsLattices























theorem omegaComb_app (u x : Pomega) :
    funOf (omegaComb u) x = funOf u (funOf x x) :=
  beta (theorem_1_3 (funOf_isScottContinuous u) diagApp_isScottContinuous) x

end DomainTheory.DataTypesAsLattices
