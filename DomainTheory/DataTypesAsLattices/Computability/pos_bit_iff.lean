/-ai
A natural number n has a set bit at some position at least 1 if and only if 2 ≤ n.

A set bit at position k + 1 gives 2^(k + 1) ≤ n, and 2^1 ≤ 2^(k + 1). Conversely, if every bit at a positive position is unset, the high-bit bound yields n < 2. The position 0 is excluded from that bound because it is below 1, so the hypothesis that the index is at least 1 is impossible there.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.lt_two_pow_of_high_bits

@[expose] public section


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
