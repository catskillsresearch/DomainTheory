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
import DomainTheory.Neighborhood.Exercise515.mem_star
import DomainTheory.Neighborhood.Exercise515.mem_kpow_singleton


namespace DomainTheory.Neighborhood.Exercise515

open Pointwise
open DomainTheory.Neighborhood.Exercise414

variable {S : Type*} [Monoid S]









/-- `{e}* = e* = {Λ, e, e², …}`: a point lies in `star {e}` iff it is some power of `e`. -/
theorem mem_star_singleton (e s : S) : s ∈ star ({e} : Set S) ↔ ∃ n, s = e ^ n := by
  rw [mem_star]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_kpow_singleton e s n).mp hn⟩
  · rintro ⟨n, rfl⟩; exact ⟨n, (mem_kpow_singleton e (e ^ n) n).mpr rfl⟩

end DomainTheory.Neighborhood.Exercise515
