/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices





































theorem triangle_eq_zero {w : ℕ} (h : triangle w = 0) : w = 0 := by
  match w with
  | 0 => rfl
  | n + 1 =>
    have h1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have h2 : 2 ≤ (n + 1) * (n + 2) :=
      calc 2 ≤ 1 * 2 := by decide
           _ ≤ (n + 1) * (n + 2) := Nat.mul_le_mul h1 (Nat.succ_le_succ h1)
    have : 0 < (n + 1) * (n + 2) / 2 := Nat.div_pos h2 (by decide)
    exact (Nat.ne_of_gt this h).elim

end DomainTheory.DataTypesAsLattices
