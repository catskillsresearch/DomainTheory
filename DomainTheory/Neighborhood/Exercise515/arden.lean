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
import DomainTheory.Neighborhood.Exercise515.star_mul_isFixed
import DomainTheory.Neighborhood.Exercise515.star_mul_subset_prefixed


namespace DomainTheory.Neighborhood.Exercise515

open Pointwise
open DomainTheory.Neighborhood.Exercise414

variable {S : Type*} [Monoid S]








/-- **Arden's lemma.** The least solution of `w = z·w ∪ v` in `P S` is `z*·v`. (Stated via
`lfpSet`, Exercise 4.14; the proof uses neither `Monotone` nor `⋃` order lemmas, so it is
choice-free.) -/
theorem arden (z v : Set S) : lfpSet (G z v) = star z * v := by
  apply Set.Subset.antisymm
  · exact lfpSet_least (G z v) (star_mul_isFixed z v)
  · intro s hs x hx
    exact star_mul_subset_prefixed z v x hx hs

end DomainTheory.Neighborhood.Exercise515
