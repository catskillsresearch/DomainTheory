/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import Mathlib.Computability.Partrec
import Mathlib.Tactic.Ring
import DomainTheory.Neighborhood.Exercise722Regular
import DomainTheory.Neighborhood.Exercise722Decide
import DomainTheory.Neighborhood.Exercise722Equiv
import DomainTheory.Neighborhood.Recursive.Basic
import DomainTheory.Neighborhood.Recursive.existsListStp_eq


namespace Domain.Recursive













































































































































theorem existsListChar_le_one (g : ℕ → ℕ) (p c : ℕ) : existsListChar g p c ≤ 1 := by
  have h : ∀ (l : List ℕ) (z : ℕ), z ≤ 1 →
      List.foldl (fun acc x => existsListStp g (Nat.pair x (Nat.pair acc p))) z l ≤ 1 := by
    intro l
    induction l with
    | nil => intro z hz; simpa using hz
    | cons x xs ih =>
      intro z hz
      simp only [List.foldl_cons]
      apply ih
      rw [existsListStp_eq]
      rcases (show z = 0 ∨ z = 1 by omega) with h0 | h1
      · rw [h0, selectFn_zero]; exact isOne_le_one _
      · rw [h1, selectFn_one]
  unfold existsListChar
  rw [foldCode_eq']
  exact h (decodeList c) 0 (Nat.zero_le 1)

end Domain.Recursive
