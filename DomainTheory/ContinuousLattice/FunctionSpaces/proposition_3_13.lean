module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.projection
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem proposition_3_13 (_hD : ContinuousLattice D) :
    Nonempty (IsContinuousLatticeProjection D (ScottMap D D)) :=
  ⟨Proposition313.projection⟩

end DomainTheory.ContinuousLattice
