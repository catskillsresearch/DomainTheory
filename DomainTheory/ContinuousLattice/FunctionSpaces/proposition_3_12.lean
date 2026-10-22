module
public import DomainTheory.ContinuousLattice.FunctionSpaces.instCompleteLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.Projections
public import DomainTheory.ContinuousLattice.FunctionSpaces.isProjection_sSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst30
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


/-- **Scott 1972, Proposition 3.12.** For a (complete, in particular continuous) lattice `D`, the
projections `J_D` form a complete lattice as a `⊔`-closed subspace of `[D → D]`: the `⊔`-closure is
`isProjection_sSup`, and the complete-lattice structure is `Projections.instCompleteLattice`. -/
theorem proposition_3_12 :
    (∀ T : Set (ScottMap D D), (∀ j ∈ T, IsProjection j) → IsProjection (sSup T))
      ∧ Nonempty (CompleteLattice (Projections D)) :=
  ⟨fun _ h => isProjection_sSup h, ⟨Projections.instCompleteLattice⟩⟩

end Projections
end DomainTheory.ContinuousLattice
