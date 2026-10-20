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
import DomainTheory.Neighborhood.Exercise515.smul_assoc
import DomainTheory.Neighborhood.Exercise515.mem_star


namespace DomainTheory.Neighborhood.Exercise515

open Pointwise
open DomainTheory.Neighborhood.Exercise414

variable {S : Type*} [Monoid S]






/-- For any prefixed point `w₀` of `w ↦ z·w ∪ v` (i.e. `z·w₀ ∪ v ⊆ w₀`), the candidate `z*·v` is
below `w₀`: the induction `zⁿ·v ⊆ w₀`. -/
theorem star_mul_subset_prefixed (z v x : Set S) (hx : z * x ∪ v ⊆ x) : star z * v ⊆ x := by
  have hvx : v ⊆ x := Set.subset_union_right.trans hx
  have hzx : z * x ⊆ x := Set.subset_union_left.trans hx
  have hpow : ∀ n, kpow z n * v ⊆ x := by
    intro n
    induction n with
    | zero => rw [kpow_zero, one_mul]; exact hvx
    | succ m ih =>
        rw [kpow_succ, smul_assoc]
        exact (Set.mul_subset_mul_left ih).trans hzx
  intro s hs
  rw [Set.mem_mul] at hs
  obtain ⟨a, ha, t, ht, rfl⟩ := hs
  obtain ⟨n, hn⟩ := mem_star.mp ha
  exact hpow n (by rw [Set.mem_mul]; exact ⟨a, hn, t, ht, rfl⟩)

end DomainTheory.Neighborhood.Exercise515
