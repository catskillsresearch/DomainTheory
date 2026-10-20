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
import DomainTheory.Neighborhood.Exercise515.part1


namespace DomainTheory.Neighborhood.Exercise515

open Pointwise
open DomainTheory.Neighborhood.Exercise414

variable {S : Type*} [Monoid S]









/-- The free semigroup `{0,1}*` of the exercise. Part (1) holds here as a special case. -/
theorem part1_freeMonoid (e e' : FreeMonoid Bool) :
    lfpSet (fun w => ({e} : Set (FreeMonoid Bool)) * w ∪ {e'})
      = star ({e} : Set (FreeMonoid Bool)) * {e'} :=
  part1 e e'

end DomainTheory.Neighborhood.Exercise515
