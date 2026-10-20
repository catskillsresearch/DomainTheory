/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.WayBelow
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.DirSupClosed
import DomainTheory.ContinuousLattice.Specialization.Basic
import DomainTheory.ContinuousLattice.Specialization.scottOpen_not_le


namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]







variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]



variable {x : ι → D} {L y : D}

omit [IsDirected ι (· ≤ ·)] in
/-- **Scott 1972, Proposition 2.1 (forward).** If a monotone net converges to `y` in the Scott
topology and `L` is its least upper bound, then `y ≤ L`. -/
theorem proposition_2_1_le_of_converges (hL : IsLUB (range x) L)
    (hconv : ScottConvergesTo x y) : y ≤ L := by
  by_contra hyL
  obtain ⟨i, hi⟩ := hconv {z : D | ¬ z ≤ L} (scottOpen_not_le L) hyL
  exact hi i le_rfl (hL.1 ⟨i, rfl⟩)

end DomainTheory.ContinuousLattice
