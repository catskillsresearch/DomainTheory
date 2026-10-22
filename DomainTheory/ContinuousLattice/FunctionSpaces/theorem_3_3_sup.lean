module

public import DomainTheory.ContinuousLattice.FunctionSpaces.sup
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

/-- **Scott 1972, Theorem 3.3 (binary join).** Pointwise join of Scott-continuous maps is
Scott-continuous. -/
noncomputable def theorem_3_3_sup (f g : ScottMap D D') : ScottMap D D' :=
  ScottMap.sup f g

end DomainTheory.ContinuousLattice
