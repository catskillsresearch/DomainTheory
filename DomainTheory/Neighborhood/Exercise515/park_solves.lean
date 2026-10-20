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
import DomainTheory.Neighborhood.Exercise515.parkX_eq
import DomainTheory.Neighborhood.Exercise515.parkY_eq


namespace DomainTheory.Neighborhood.Exercise515

open Pointwise
open DomainTheory.Neighborhood.Exercise414

variable {S : Type*} [Monoid S]














/-- **Exercise 5.15(2), existence.** `(x₀, y₀)` solves David Park's system. -/
theorem park_solves (a b c d : Set S) :
    parkX a b c d = a * parkX a b c d ∪ b * parkY a b c d ∪ c ∧
      parkY a b c d = b * parkX a b c d ∪ a * parkY a b c d ∪ d :=
  ⟨parkX_eq a b c d, parkY_eq a b c d⟩

end DomainTheory.Neighborhood.Exercise515
