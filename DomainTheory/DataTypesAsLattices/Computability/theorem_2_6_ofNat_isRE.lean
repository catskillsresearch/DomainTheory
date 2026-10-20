/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.IsREu2enumeral


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




/-- **Scott 1976, Theorem 2.6, r.e. direction for numerals.** -/
theorem theorem_2_6_ofNat_isRE (n : ℕ) : IsCombinatory (ofNat n) → IsRE (ofNat n) :=
  fun _ => IsRE.numeral n

end DomainTheory.DataTypesAsLattices
