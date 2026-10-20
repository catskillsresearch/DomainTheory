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
import DomainTheory.Neighborhood.Exercise417.F_monotone


namespace DomainTheory.Neighborhood.Exercise417

open Pointwise
open DomainTheory.Neighborhood.Exercise414

variable {S : Type*} [Monoid S]






/-- The least solution `lfpSet (F a b)` indeed solves Scott's equation `x = {1} ∪ {a, b} ∪ x · x`. -/
theorem leastSolution_eq (a b : S) :
    F a b (lfpSet (F a b)) = lfpSet (F a b) :=
  lfpSet_isFixed (F a b) (F_monotone a b)

end DomainTheory.Neighborhood.Exercise417
