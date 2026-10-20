/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.evalC_isScottContinuous


namespace DomainTheory.DataTypesAsLattices

















theorem evalC_app (u : Pomega) :
    funOf evalC u = funOf (funOf u (ofNat 0)) (funOf u (ofNat 1)) :=
  beta evalC_isScottContinuous u

end DomainTheory.DataTypesAsLattices
