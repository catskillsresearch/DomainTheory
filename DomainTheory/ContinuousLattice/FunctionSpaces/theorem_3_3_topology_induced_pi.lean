/-ai
If D and D' are continuous lattices, the Scott topology on the space of Scott maps is the topology induced from the product topology on the underlying functions.

The Scott topology equals the pointwise topology by Theorem 3.3, and the pointwise topology equals the induced product topology.
ai-/
module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapPointwiseTopology_eq_induced_pi
public import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_topology

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


/-- The literal product/subspace form of Theorem 3.3: the Scott lattice topology on `[D → D']`
is induced from Mathlib's Pi topology on the underlying functions. -/
theorem theorem_3_3_topology_induced_pi (hD : ContinuousLattice D)
    (hD' : ContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) =
      scottMapInducedPiTopology D D' := by
  rw [theorem_3_3_topology hD hD', scottMapPointwiseTopology_eq_induced_pi]

end DomainTheory.ContinuousLattice
