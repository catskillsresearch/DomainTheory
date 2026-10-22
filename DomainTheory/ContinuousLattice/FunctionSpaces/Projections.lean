module

public import DomainTheory.ContinuousLattice.FunctionSpaces.IsProjection
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

section Projections

/-- **Scott 1972, Definition 3.11.** The space `J_D` of projections of `D`, as a subtype of
`[D → D]`. -/
abbrev Projections (D : Type*) [CompleteLattice D] : Type _ := {j : ScottMap D D // IsProjection j}

end Projections

end DomainTheory.ContinuousLattice
