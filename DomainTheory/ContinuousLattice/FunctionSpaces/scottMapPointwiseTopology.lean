module

public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapPointwiseSubbasis
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

@[reducible] noncomputable def scottMapPointwiseTopology (D D' : Type*)
    [CompleteLattice D] [CompleteLattice D'] : TopologicalSpace (ScottMap D D') :=
  generateFrom (scottMapPointwiseSubbasis D D')

end DomainTheory.ContinuousLattice
