module

public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import Mathlib.Topology.Order.ScottTopology
public import DomainTheory.ContinuousLattice.Specialization.isOpen_iff_scottOpen
public import Mathlib.Data.Set.Basic

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
