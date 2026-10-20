/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices





/-- **Scott 1976, (3.2).** `cond(x)(y)(0) = x`. -/
theorem eq_3_2 (x y : Pomega) :
    funOf (funOf (funOf condC x) y) zeroC = x := by
  rw [condC_beta3]
  have : zeroC = ofNat 0 := rfl
  simpa [this] using eq_2_7_zero x y

end DomainTheory.DataTypesAsLattices
