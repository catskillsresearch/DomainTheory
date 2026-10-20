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

theorem pos_bit_iff (n : ℕ) :
    (∃ k, n.testBit (k + 1) = true) ↔ 2 ≤ n := by
  constructor
  · intro ⟨k, hk⟩
    exact (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (Nat.le_add_left 1 k) : (2 : ℕ) ^ 1 ≤ 2 ^ (k + 1)).trans
      (two_pow_le_of_testBit hk)
  · intro hn
    by_contra hex
    push Not at hex
    have hlt : n < 2 := lt_two_pow_of_high_bits fun j hj => by
      cases j with
      | zero => exact (Nat.not_succ_le_zero 0 hj).elim
      | succ j => exact Bool.eq_false_iff.2 (hex j)
    exact Nat.not_lt.mpr hn hlt

end DomainTheory.DataTypesAsLattices
