module

public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst30
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_directedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_finsetSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.directedOn_finsetSupOf
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_finsetSupOf
public import Mathlib.Topology.Defs.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

section Projections

/-- **Scott 1972, Proposition 3.12 (`⊔`-closure).** `J_D` is closed under arbitrary suprema in
`[D → D]`: every supremum is the directed supremum of finite sub-joins (`finsetSupOf`), each a
projection by `isProjection_finsetSup`. -/
theorem isProjection_sSup {T : Set (ScottMap D D)} (hT : ∀ j ∈ T, IsProjection j) :
    IsProjection (sSup T) := by
  rw [IsContinuousLatticeProjection.sSup_finsetSupOf T]
  refine isProjection_directedSup ⟨⊥, ∅, by simp, by simp⟩
    (IsContinuousLatticeProjection.directedOn_finsetSupOf T) ?_
  rintro z ⟨F, hF, rfl⟩
  exact isProjection_finsetSup fun j hj => hT j (hF j hj)

end Projections

end DomainTheory.ContinuousLattice
