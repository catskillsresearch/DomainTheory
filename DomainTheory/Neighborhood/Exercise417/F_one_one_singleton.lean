/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise414
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Nat.Defs
import DomainTheory.Neighborhood.Exercise417.Basic


namespace DomainTheory.Neighborhood.Exercise417

open Pointwise
open DomainTheory.Neighborhood.Exercise414

variable {S : Type*} [Monoid S]








/-- `{1}` is a fixed point of `F 1 1`: `{1} ∪ {1, 1} ∪ {1}·{1} = {1}`. -/
theorem F_one_one_singleton : F (1 : ℕ) 1 ({1} : Set ℕ) = {1} := by
  unfold F
  rw [Set.singleton_mul_singleton]
  simp

end DomainTheory.Neighborhood.Exercise417
