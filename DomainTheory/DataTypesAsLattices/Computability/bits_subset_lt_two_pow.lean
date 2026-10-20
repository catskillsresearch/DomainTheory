/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.lt_two_pow_of_high_bits


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem bits_subset_lt_two_pow {n b : ℕ} (h : e n ⊆ e b) : n < 2 ^ (b + 1) :=
  lt_two_pow_of_high_bits fun _j hj =>
    Bool.eq_false_iff.2 fun hbit =>
      Nat.not_le.mpr hj (mem_e_le (h (mem_e.mpr hbit)))

end DomainTheory.DataTypesAsLattices
