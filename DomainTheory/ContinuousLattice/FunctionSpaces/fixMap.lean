module

public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_preservesDirectedSup
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

namespace Proposition314

noncomputable def fixMap : ScottMap (ScottMap D D) D :=
  ⟨fix, continuous_of_preservesDirectedSup fix_preservesDirectedSup⟩

end Proposition314

end DomainTheory.ContinuousLattice
