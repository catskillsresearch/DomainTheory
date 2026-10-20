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


































/-- **Scott 1976, (3.8).** `apply(0)(0) = 1` and `val(1) = 0`. -/
theorem eq_3_8_apply : applyNat 0 0 = 1 := by simp [applyNat, pair]

end DomainTheory.DataTypesAsLattices
