module

public import DomainTheory.ContinuousLattice.WayBelow
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.DirSupClosed
public import DomainTheory.ContinuousLattice.Specialization.SpecializationLe
public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.Specialization.MonotoneNet
public import DomainTheory.ContinuousLattice.Specialization.ScottConvergesTo
public import DomainTheory.ContinuousLattice.Specialization.specializationPreorder

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]


variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]


variable {x : ι → D} {L y : D}
end DomainTheory.ContinuousLattice
