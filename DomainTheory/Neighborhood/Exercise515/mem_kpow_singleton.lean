/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise414
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import DomainTheory.Neighborhood.Exercise515.Basic


namespace DomainTheory.Neighborhood.Exercise515

open Pointwise
open DomainTheory.Neighborhood.Exercise414

variable {S : Type*} [Monoid S]









/-- `{e}ⁿ = {eⁿ}` at the membership level (choice-free). -/
theorem mem_kpow_singleton (e s : S) (n : ℕ) : s ∈ kpow ({e} : Set S) n ↔ s = e ^ n := by
  induction n generalizing s with
  | zero => rw [kpow_zero, pow_zero]; exact Set.mem_one
  | succ m ih =>
      rw [kpow_succ, pow_succ', Set.mem_mul]
      constructor
      · rintro ⟨a, ha, t, ht, rfl⟩
        rw [Set.mem_singleton_iff] at ha
        rw [(ih t).mp ht, ha]
      · rintro rfl
        exact ⟨e, Set.mem_singleton_iff.mpr rfl, e ^ m, (ih (e ^ m)).mpr rfl, rfl⟩

end DomainTheory.Neighborhood.Exercise515
