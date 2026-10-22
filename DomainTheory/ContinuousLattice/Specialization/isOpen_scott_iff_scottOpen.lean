module

public import DomainTheory.ContinuousLattice.WayBelow
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.DirSupClosed
public import DomainTheory.ContinuousLattice.Specialization.Basic
public import DomainTheory.ContinuousLattice.Specialization.isOpen_iff_scottOpen

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]


/-- Scott-open sets in our sense agree with mathlib's Scott topology (alias). -/
theorem isOpen_scott_iff_scottOpen {U : Set D} :
    @IsOpen D (Topology.scott D univ) U ↔ ScottOpen U :=
  isOpen_iff_scottOpen

end DomainTheory.ContinuousLattice
