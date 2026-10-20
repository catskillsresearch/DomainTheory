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
import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_8_val
import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_9_apply


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


































theorem eq_3_9_val : valNat 3 = Gpack := by
  have : valNat 3 = valNat (applyNat 0 1) := by simp [eq_3_9_apply]
  rw [this, valNat_apply, valNat_zero, eq_3_8_val]
  have : zeroC = ofNat 0 := rfl
  simpa [this] using Gcomb_zero

end DomainTheory.DataTypesAsLattices
