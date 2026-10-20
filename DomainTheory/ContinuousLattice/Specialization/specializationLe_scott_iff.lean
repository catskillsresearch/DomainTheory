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
import DomainTheory.ContinuousLattice.Specialization.isOpen_iff_scottOpen
import DomainTheory.ContinuousLattice.Specialization.scottOpen_not_le


namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]







variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]



variable {x : ι → D} {L y : D}

/-- The specialization order of the Scott topology is the original lattice order. -/
theorem specializationLe_scott_iff {x y : D} :
    @SpecializationLe D scottTopologicalSpace x y ↔ x ≤ y := by
  constructor
  · intro hxy
    by_contra h
    exact hxy {z | ¬ z ≤ y} (isOpen_iff_scottOpen.mpr (scottOpen_not_le y)) h (by simp)
  · intro hxy U hU hxU
    exact (isOpen_iff_scottOpen.mp hU).1 hxy hxU

end DomainTheory.ContinuousLattice
