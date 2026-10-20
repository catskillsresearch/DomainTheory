/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_left
import DomainTheory.DataTypesAsLattices.Lambda.condC_beta2


namespace DomainTheory.DataTypesAsLattices

































theorem condC_beta3 (x y z : Pomega) :
    funOf (funOf (funOf condC x) y) z = condSet z x y := by
  rw [condC_beta2]
  exact beta (condSet_isScottContinuous_left x y) z

end DomainTheory.DataTypesAsLattices
