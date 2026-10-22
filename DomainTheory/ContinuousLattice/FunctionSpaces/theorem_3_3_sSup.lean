module

public import DomainTheory.ContinuousLattice.FunctionSpaces.sSupMaps
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

/-- **Scott 1972, Theorem 3.3 (directed sup).** Pointwise suprema of Scott-continuous maps are
Scott-continuous; this is the heart of Scott's proof that `[D → D']` is a complete lattice. -/
noncomputable def theorem_3_3_sSup (F : Set (ScottMap D D')) : ScottMap D D' :=
  ScottMap.sSupMaps F

end DomainTheory.ContinuousLattice
