module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap

@[expose] public section

namespace DomainTheory.ContinuousLattice

variable {D₀ D₀' D₁ D₁' : Type*}

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace ScottMap

structure retraction (D₀ D₀' D₁ D₁' : Type*)
    [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁'] where
  incl : ScottMap D₀ D₁ → ScottMap D₀' D₁'
  retr : ScottMap D₀' D₁' → ScottMap D₀ D₁
  retr_incl : ∀ f, retr (incl f) = f

end ScottMap

end DomainTheory.ContinuousLattice
