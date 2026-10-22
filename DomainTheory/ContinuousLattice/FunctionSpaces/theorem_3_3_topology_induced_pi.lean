module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_topology
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapPointwiseTopology_eq_induced_pi
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapInducedPiTopology
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import Mathlib.Topology.Defs.Basic

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
