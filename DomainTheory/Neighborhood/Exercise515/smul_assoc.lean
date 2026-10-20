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


/-- Associativity of the pointwise product (membership proof, choice-free). -/
theorem smul_assoc (a b c : Set S) : a * b * c = a * (b * c) := by
  ext s; simp only [Set.mem_mul]
  constructor
  · rintro ⟨u, ⟨p, hp, q, hq, rfl⟩, w, hw, rfl⟩
    exact ⟨p, hp, q * w, ⟨q, hq, w, hw, rfl⟩, by rw [mul_assoc]⟩
  · rintro ⟨p, hp, u, ⟨q, hq, w, hw, rfl⟩, rfl⟩
    exact ⟨p * q, ⟨p, hp, q, hq, rfl⟩, w, hw, by rw [mul_assoc]⟩

end DomainTheory.Neighborhood.Exercise515
