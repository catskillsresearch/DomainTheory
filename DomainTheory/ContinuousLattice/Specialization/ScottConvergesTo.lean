module

public import DomainTheory.ContinuousLattice.WayBelow
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.DirSupClosed
public import DomainTheory.ContinuousLattice.Specialization.specializationPreorder

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]

def ScottConvergesTo (x : ι → D) (y : D) : Prop :=
  ∀ U, ScottOpen U → y ∈ U → ∃ i, ∀ j ≥ i, x j ∈ U

end DomainTheory.ContinuousLattice
