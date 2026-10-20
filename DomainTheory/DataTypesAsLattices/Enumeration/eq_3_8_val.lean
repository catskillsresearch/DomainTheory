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
import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_8_apply


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


































theorem eq_3_8_val : valNat 1 = zeroC := by
  have : valNat 1 = valNat (applyNat 0 0) := by simp [eq_3_8_apply]
  rw [this, valNat_apply, valNat_zero, Gcomb_app_self]

end DomainTheory.DataTypesAsLattices
