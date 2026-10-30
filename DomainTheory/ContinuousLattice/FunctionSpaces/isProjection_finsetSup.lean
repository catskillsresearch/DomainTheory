module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_sup
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_bot
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Finset.Basic

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

section Projections

theorem isProjection_finsetSup {T : Finset (ScottMap D D)} (hT : ∀ j ∈ T, ScottMap.IsProjection j) :
    ScottMap.IsProjection (T.sup id) :=
  Finset.sup_induction isProjection_bot (fun _ ha _ hb => isProjection_sup ha hb) hT

end Projections

end DomainTheory.ContinuousLattice
