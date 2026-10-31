module

public import DomainTheory.ContinuousLattice.FunctionSpaces.FunctionSpace

@[expose] public section

namespace DomainTheory.ContinuousLattice

variable {D₀ D₀' D₁ D₁' : Type*}

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem proposition_3_7 (P₀ : ContinuousLatticeProjection D₀ D₀') (P₁ : ContinuousLatticeProjection D₁ D₁') :
    Nonempty (ScottMap.retraction D₀ D₀' D₁ D₁') ∧
    Nonempty (ScottMap.projection D₀ D₀' D₁ D₁') :=
  ⟨⟨FunctionSpace.retraction P₀.toContinuousLatticeRetraction P₁.toContinuousLatticeRetraction⟩,
   ⟨FunctionSpace.projection P₀ P₁⟩⟩

end DomainTheory.ContinuousLattice
