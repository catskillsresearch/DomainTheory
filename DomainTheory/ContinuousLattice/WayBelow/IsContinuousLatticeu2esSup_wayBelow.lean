/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import DomainTheory.ContinuousLattice.WayBelow.Basic


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]





/-- In a continuous lattice, `y` is the actual supremum of `{x | x ≪ y}`. -/
theorem IsContinuousLattice.sSup_wayBelow (h : IsContinuousLattice D) (y : D) :
    sSup {x | x ≪ y} = y :=
  (h y).sSup_eq

end DomainTheory.ContinuousLattice
