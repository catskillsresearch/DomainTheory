/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem85
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import DomainTheory.Neighborhood.Exercise811.Basic


namespace DomainTheory.Neighborhood.Exercise811

open NeighborhoodSystem ApproximableMap











theorem aRel_le {r s : ℚ} (h : r < s ∨ (r = 1 ∧ s = 1)) : r ≤ s := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact h.le
  · exact le_rfl

end DomainTheory.Neighborhood.Exercise811
