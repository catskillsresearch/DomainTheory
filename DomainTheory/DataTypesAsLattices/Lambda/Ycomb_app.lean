/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.diagApp_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.omegaComb_isScottContinuous


namespace DomainTheory.DataTypesAsLattices























theorem Ycomb_app (u : Pomega) :
    funOf Ycomb u = funOf (omegaComb u) (omegaComb u) :=
  beta (theorem_1_3 diagApp_isScottContinuous omegaComb_isScottContinuous) u

end DomainTheory.DataTypesAsLattices
