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
import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_10_val


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

















































/-- **Scott 1976, (3.12).** `val(num(n)) = n`. -/
theorem eq_3_12 : ∀ n, valNat (num n) = ofNat n
  | 0 => eq_3_8_val
  | n + 1 => by
    rw [num, valNat_apply, eq_3_10_val, eq_3_12, sucC_app, succSet_ofNat]

end DomainTheory.DataTypesAsLattices
