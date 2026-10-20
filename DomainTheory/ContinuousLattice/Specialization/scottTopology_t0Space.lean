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
import DomainTheory.ContinuousLattice.Specialization.specializationLe_scott_iff


namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]







variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]



variable {x : ι → D} {L y : D}

/-- The Scott topology of a partial order is `T₀`. -/
theorem scottTopology_t0Space : @T0Space D scottTopologicalSpace := by
  let : TopologicalSpace D := scottTopologicalSpace
  constructor
  intro x y hxy
  apply le_antisymm
  · rw [← specializationLe_scott_iff]
    intro U hU hxU
    exact (hxy.mem_open_iff hU).mp hxU
  · rw [← specializationLe_scott_iff]
    intro U hU hyU
    exact (hxy.mem_open_iff hU).mpr hyU

end DomainTheory.ContinuousLattice
