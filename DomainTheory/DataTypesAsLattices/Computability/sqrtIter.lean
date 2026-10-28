module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Computability.pack4

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

def sqrtIter (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      let a := sqrtIter n k
      if (a + 1) * (a + 1) ≤ n then a + 1 else a

namespace sqrtIter

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem eq_min (n k : ℕ) : sqrtIter n k = min k (Nat.sqrt n) := by
  induction k with
  | zero => simp [sqrtIter]
  | succ k ih =>
    rw [sqrtIter, ih]
    by_cases h : k < Nat.sqrt n
    · have hmin : min k (Nat.sqrt n) = k := min_eq_left h.le
      have hs : (k + 1) * (k + 1) ≤ n := Nat.le_sqrt.mp h
      simp [hmin, hs, min_eq_left (Nat.succ_le_iff.mpr h)]
    · have hk : Nat.sqrt n ≤ k := Nat.le_of_not_gt h
      have hmin : min k (Nat.sqrt n) = Nat.sqrt n := min_eq_right hk
      have hs : ¬(Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ n :=
        Nat.not_le.mpr (Nat.lt_succ_sqrt n)
      simp [hmin, hs, min_eq_right (hk.trans (Nat.le_succ k))]

theorem self (n : ℕ) : sqrtIter n n = Nat.sqrt n := by
  rw [sqrtIter.eq_min, min_eq_right (Nat.sqrt_le_self n)]

end sqrtIter

end DomainTheory.DataTypesAsLattices
