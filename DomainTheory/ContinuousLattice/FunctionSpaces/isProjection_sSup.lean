module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_directedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_finsetSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeRetractionProjection
public import Mathlib.Topology.Defs.Basic

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

section Projections

theorem isProjection_sSup {T : Set (ScottMap D D)} (hT : ∀ j ∈ T, ScottMap.IsProjection j) :
    ScottMap.IsProjection (sSup T) := by
  rw [ContinuousLatticeProjection.sSup_finsetSupOf T]
  refine isProjection_directedSup ⟨⊥, ∅, by simp, by simp⟩
    (ContinuousLatticeProjection.directedOn_finsetSupOf T) ?_
  rintro z ⟨F, hF, rfl⟩
  exact isProjection_finsetSup fun j hj => hT j (hF j hj)

end Projections

end DomainTheory.ContinuousLattice
