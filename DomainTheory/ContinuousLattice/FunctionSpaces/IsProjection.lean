module

public import DomainTheory.ContinuousLattice.FunctionSpaces.comp
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst28
public import DomainTheory.ContinuousLattice.FunctionSpaces.idMap
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

def IsProjection (j : ScottMap D D) : Prop :=
  j.comp j = j ∧ j ≤ ScottMap.idMap

end Projections

end DomainTheory.ContinuousLattice
