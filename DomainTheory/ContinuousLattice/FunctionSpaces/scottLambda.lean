module

public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambdaAt
public import DomainTheory.ContinuousLattice.FunctionSpaces.lambda_outer_preservesDirectedSup
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

/-- **Scott 1972, Proposition 3.5.** Functional abstraction
`lambda : [[D × D'] → D''] → [D → [D' → D'']]`, `lambda f x y = f (x, y)`. By Theorem 3.3,
`[D → [D' → D'']]` is itself a continuous lattice, and `lambda f` is a Scott map. -/
noncomputable def scottLambda (f : ScottMap (D × D') D'') : ScottMap D (ScottMap D' D'') :=
  ⟨fun x => scottLambdaAt f x,
    continuous_of_preservesDirectedSup (lambda_outer_preservesDirectedSup f)⟩

end DomainTheory.ContinuousLattice
