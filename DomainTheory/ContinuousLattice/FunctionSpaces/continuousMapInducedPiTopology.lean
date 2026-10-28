module
public import Mathlib.Topology.Constructions
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.CompleteLattice.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

@[reducible] noncomputable def continuousMapInducedPiTopology (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y] : TopologicalSpace C(X, Y) :=
  TopologicalSpace.induced (fun f : C(X, Y) => (f : X → Y))
    (@Pi.topologicalSpace X (fun _ => Y) (fun _ => inferInstance))

end DomainTheory.ContinuousLattice
