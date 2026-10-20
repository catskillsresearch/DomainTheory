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


theorem F_monotone (a b : S) : Monotone (F a b) := by
  intro x y hxy
  exact Set.union_subset_union (le_refl _) (Set.mul_subset_mul hxy hxy)

end DomainTheory.Neighborhood.Exercise417
