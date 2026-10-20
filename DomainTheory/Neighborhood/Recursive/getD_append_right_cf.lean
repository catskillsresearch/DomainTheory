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


namespace Domain.Recursive





































































































































































/-- Choice-free `getD` of a right append. -/
theorem getD_append_right_cf {β : Type*} (l l' : List β) (d : β) :
    ∀ {n : ℕ}, l.length ≤ n → (l ++ l').getD n d = l'.getD (n - l.length) d := by
  induction l with
  | nil => intro n _; rw [List.nil_append, List.length_nil, Nat.sub_zero]
  | cons a t ih =>
    intro n h
    cases n with
    | zero => exact absurd h (by rw [List.length_cons]; exact Nat.not_succ_le_zero _)
    | succ m =>
      rw [List.cons_append, List.getD_cons_succ, List.length_cons, Nat.succ_sub_succ]
      exact ih (by rw [List.length_cons] at h; omega)

end Domain.Recursive
