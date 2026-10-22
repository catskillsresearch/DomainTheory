/-ai
If U is open in the Scott topology of D', then for each element x the set of Scott maps whose value at x lies in U is open in the pointwise topology on the function space.

That set is one of the subbasic sets that generate the pointwise topology.
ai-/
module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


theorem pointwiseSubbasic_isOpen (x : D) {U : Set D'} (hU : @IsOpen D' scottTopologicalSpace U) :
    @IsOpen (ScottMap D D') (scottMapPointwiseTopology D D')
      {f : ScottMap D D' | (f : D → D') x ∈ U} :=
  isOpen_generateFrom_of_mem ⟨x, U, hU, rfl⟩

end DomainTheory.ContinuousLattice
