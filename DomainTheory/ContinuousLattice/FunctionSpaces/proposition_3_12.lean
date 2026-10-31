module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ProjectionSpace

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

variable {D : Type*} [CompleteLattice D]

theorem proposition_3_12 :
    (∀ T : Set (ScottMap D D), (∀ j ∈ T, ProjectionSpace.mem j) → ProjectionSpace.mem (sSup T))
      ∧ Nonempty (CompleteLattice (ProjectionSpace D)) :=
  ⟨fun _ h => ProjectionSpace.sSup_mem h, ⟨ProjectionSpace.instCompleteLattice⟩⟩

end DomainTheory.ContinuousLattice
