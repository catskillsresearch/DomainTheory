/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.curry_body_isScottContinuous_y
import DomainTheory.DataTypesAsLattices.Functionality.curryC_app2


namespace DomainTheory.DataTypesAsLattices

















theorem curryC_app3 (u x y : Pomega) :
    funOf (funOf (funOf curryC u) x) y = funOf u (pairSeq x y) := by
  rw [curryC_app2]
  exact beta (curry_body_isScottContinuous_y u x) y

end DomainTheory.DataTypesAsLattices
