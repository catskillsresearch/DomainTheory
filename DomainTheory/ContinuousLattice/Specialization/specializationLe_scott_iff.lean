module

public import DomainTheory.ContinuousLattice.Specialization.SpecializationLe
public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.Specialization.scottOpen_not_le
public import DomainTheory.ContinuousLattice.Specialization.isOpen_iff_scottOpen
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section


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
