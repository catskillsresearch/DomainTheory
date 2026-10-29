module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottFunctionTopology
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import Mathlib.Topology.Defs.Basic

public import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_more

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem theorem_3_3 (hD : ContinuousLattice D) (hD' : ContinuousLattice D') :
    ContinuousLattice (ScottMap D D') ∧
      (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) = scottMapPointwiseTopology D D' :=
  ⟨theorem_3_3.isContinuousLattice hD hD', theorem_3_3.topology hD hD'⟩

end DomainTheory.ContinuousLattice
