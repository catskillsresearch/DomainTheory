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


/-- Left distributivity `a·(b ∪ c) = a·b ∪ a·c` (choice-free). -/
theorem smul_union (a b c : Set S) : a * (b ∪ c) = a * b ∪ a * c := by
  ext s; simp only [Set.mem_mul, Set.mem_union]
  constructor
  · rintro ⟨u, hu, w, (hw | hw), rfl⟩
    · exact Or.inl ⟨u, hu, w, hw, rfl⟩
    · exact Or.inr ⟨u, hu, w, hw, rfl⟩
  · rintro (⟨u, hu, w, hw, rfl⟩ | ⟨u, hu, w, hw, rfl⟩)
    · exact ⟨u, hu, w, Or.inl hw, rfl⟩
    · exact ⟨u, hu, w, Or.inr hw, rfl⟩

end DomainTheory.Neighborhood.Exercise515
