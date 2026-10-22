module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem lt_two_pow_of_high_bits {n k : ℕ}
    (h : ∀ j, k ≤ j → n.testBit j = false) : n < 2 ^ k := by
  induction n using Nat.binaryRec generalizing k with
  | zero => simp
  | bit b n ih =>
    cases k with
    | zero =>
      have hb : b = false := by
        simpa [Nat.testBit_bit_zero] using h 0 le_rfl
      have hn0 : n = 0 := Nat.zero_of_testBit_eq_false fun j => by
        simpa [Nat.testBit_bit_succ] using h (j + 1) (Nat.zero_le (j + 1))
      simp [hb, hn0]
    | succ k =>
      have : n < 2 ^ k := ih fun j hj => by
        simpa [Nat.testBit_bit_succ] using h (j + 1) (Nat.succ_le_succ hj)
      exact Nat.bit_lt_two_pow_succ_iff.mpr this

end DomainTheory.DataTypesAsLattices
