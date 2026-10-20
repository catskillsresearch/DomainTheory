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




/-- **Scott 1972, Proposition 2.2(iii).** `x ≪ y` and `y ≤ z` imply `x ≪ z` (monotone on the
right). -/
theorem WayBelow.trans_le {x y z : D} (h : x ≪ y) (hyz : y ≤ z) : x ≪ z := by
  obtain ⟨U, hU, hyU, hsub⟩ := h
  exact ⟨U, hU, hU.1 hyz hyU, hsub⟩

end DomainTheory.ContinuousLattice
