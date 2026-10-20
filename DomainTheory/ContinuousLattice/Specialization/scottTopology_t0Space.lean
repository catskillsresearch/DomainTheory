module

public import DomainTheory.ContinuousLattice.WayBelow
public import Mathlib.Topology.Inseparable
import all Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Basic
import all Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Order.ScottTopology
import all Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.DirSupClosed
import all Mathlib.Order.DirSupClosed
public import DomainTheory.ContinuousLattice.Specialization.Basic
public import DomainTheory.ContinuousLattice.Specialization.specializationLe_scott_iff

@[expose] public section


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
