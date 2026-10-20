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


































































































/-- `{0,1}`-valued `max` of two primitive-recursive functions. -/
theorem primrec_max {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => Nat.max (f n) (g n)) := by
  refine (primrec_selectFn (primrec_le hf hg) hg hf).of_eq fun n => by
    unfold selectFn isZero Nat.max
    by_cases h : f n ≤ g n
    · simp [Nat.sub_eq_zero_iff_le.mpr h, Nat.max_eq_right h]
    · have hlt : g n < f n := Nat.lt_of_not_ge h
      have hpos : 0 < f n - g n := Nat.sub_pos_of_lt hlt
      have hmin : min (f n - g n) 1 = 1 := Nat.min_eq_right (Nat.succ_le_iff.mpr hpos)
      simp [hmin, Nat.max_eq_left (Nat.le_of_lt hlt)]

end Domain.Recursive
