module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.curry_right_preservesDirectedSup
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

/-- **Scott 1972, Proposition 3.5 (right).** Currying in the `y`-variable is Scott-continuous. -/
noncomputable def scottLambdaAt (f : ScottMap (D × D') D'') (x : D) : ScottMap D' D'' :=
  ⟨fun y => f (x, y), continuous_of_preservesDirectedSup (curry_right_preservesDirectedSup f x)⟩

end DomainTheory.ContinuousLattice
