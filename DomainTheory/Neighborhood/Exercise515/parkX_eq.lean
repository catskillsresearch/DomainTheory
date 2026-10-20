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
import DomainTheory.Neighborhood.Exercise515.sunion_mul
import DomainTheory.Neighborhood.Exercise515.smul_union
import DomainTheory.Neighborhood.Exercise515.star_mul_isFixed


namespace DomainTheory.Neighborhood.Exercise515

open Pointwise
open DomainTheory.Neighborhood.Exercise414

variable {S : Type*} [Monoid S]














/-- `x₀` satisfies the first equation `x = a·x ∪ b·y ∪ c`. -/
theorem parkX_eq (a b c d : Set S) :
    parkX a b c d = a * parkX a b c d ∪ b * parkY a b c d ∪ c := by
  have hfix : parkA a b * parkX a b c d ∪ parkC a b c d = parkX a b c d :=
    star_mul_isFixed (parkA a b) (parkC a b c d)
  conv_lhs => rw [← hfix]
  simp only [parkA, parkC, parkY, sunion_mul, smul_union, smul_assoc,
    Set.union_comm, Set.union_left_comm]

end DomainTheory.Neighborhood.Exercise515
