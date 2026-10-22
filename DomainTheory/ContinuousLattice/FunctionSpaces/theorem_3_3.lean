module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_isContinuousLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_topology

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


/-- **Scott 1972, Theorem 3.3 (full statement).** For continuous lattices `D`, `D'`, the function
space `[D → D']` is a continuous lattice (`theorem_3_3_isContinuousLattice`) whose Scott topology
agrees with the topology of pointwise convergence (`theorem_3_3_topology`). -/
theorem theorem_3_3 (hD : ContinuousLattice D) (hD' : ContinuousLattice D') :
    ContinuousLattice (ScottMap D D') ∧
      (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) = scottMapPointwiseTopology D D' :=
  ⟨theorem_3_3_isContinuousLattice hD hD', theorem_3_3_topology hD hD'⟩

end DomainTheory.ContinuousLattice
