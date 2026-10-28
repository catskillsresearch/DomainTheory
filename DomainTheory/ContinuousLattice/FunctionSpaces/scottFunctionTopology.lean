module

public import Mathlib.Topology.Order
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottFunctionEvalSubbasis
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

@[reducible] noncomputable def scottFunctionTopology (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] : TopologicalSpace (C(X, Y)) :=
  generateFrom (scottFunctionEvalSubbasis X Y)

end DomainTheory.ContinuousLattice
