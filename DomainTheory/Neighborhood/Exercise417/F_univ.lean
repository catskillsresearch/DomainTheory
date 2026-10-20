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








/-- In any monoid, `Set.univ` is a fixed point of `F a b`: `s = 1 · s ∈ univ · univ`. -/
theorem F_univ (a b : S) : F a b (Set.univ : Set S) = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro s _
  exact self_mul_subset_F a b _ (Set.mem_mul.mpr ⟨1, trivial, s, trivial, one_mul s⟩)

end DomainTheory.Neighborhood.Exercise417
