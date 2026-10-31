module

public import DomainTheory.ContinuousLattice.FunctionSpaces.Retraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeRetractionProjection

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {D D₀ D₀' D₁ D₁' : Type*}

variable [CompleteLattice D] [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace ScottMap

structure projection (D₀ D₀' D₁ D₁' : Type*)
    [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁'] extends
    ScottMap.retraction D₀ D₀' D₁ D₁' where
  incl_retr_le : ∀ f' x, (incl (retr f')) x ≤ f' x

noncomputable def conMinContinuousLatticeProjection : ContinuousLatticeProjection D (ScottMap D D) where
  incl := ScottMap.con
  retr := ScottMap.min
  retr_incl := fun _ => rfl
  incl_retr_le := fun f => by
    rw [ScottMap.le_def]
    intro y
    show ((ScottMap.const ((f : D → D) ⊥) : ScottMap D D) : D → D) y ≤ (f : D → D) y
    rw [ScottMap.const_apply]
    exact f.monotone bot_le

end ScottMap

end DomainTheory.ContinuousLattice
