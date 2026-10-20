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
import DomainTheory.Neighborhood.Exercise515.star_eq


namespace DomainTheory.Neighborhood.Exercise515

open Pointwise
open DomainTheory.Neighborhood.Exercise414

variable {S : Type*} [Monoid S]






/-- `z*·v` is a fixed point of `w ↦ z·w ∪ v`: the star identity `z·(z*·v) ∪ v = z*·v`. -/
theorem star_mul_isFixed (z v : Set S) : z * (star z * v) ∪ v = star z * v := by
  conv_rhs => rw [star_eq z]
  rw [sunion_mul, one_mul, smul_assoc]
  exact Set.union_comm _ _

end DomainTheory.Neighborhood.Exercise515
