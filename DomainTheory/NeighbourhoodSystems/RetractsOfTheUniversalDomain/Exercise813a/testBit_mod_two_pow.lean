/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise812
public import DomainTheory.Neighborhood.Exercise812g4
public import DomainTheory.Neighborhood.Exercise813a.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem


/-- **`n % 2^k`'s bit `i`** is `n`'s own bit `i` when `i < k` (the low bits are preserved by
reduction mod `2^k`), and `false` otherwise (nothing above bit `k-1` survives). Proved via the
division algorithm (`Nat.div_add_mod`) fed into `Nat.testBit_two_pow_mul_add`. -/
theorem testBit_mod_two_pow (n k i : ℕ) :
    (n % 2 ^ k).testBit i = (decide (i < k) && n.testBit i) := by
  have hlt : n % 2 ^ k < 2 ^ k := Nat.mod_lt n (Nat.two_pow_pos k)
  have h := Nat.testBit_two_pow_mul_add (n / 2 ^ k) hlt i
  rw [Nat.div_add_mod] at h
  rcases Nat.lt_or_ge i k with hik | hik
  · simp only [hik, ite_true, decide_true, Bool.true_and] at h ⊢
    exact h.symm
  · simp only [Nat.not_lt.mpr hik, decide_false, Bool.false_and]
    exact Nat.testBit_eq_false_of_lt (hlt.trans_le (Nat.pow_le_pow_right (by norm_num) hik))

end DomainTheory.Neighborhood
