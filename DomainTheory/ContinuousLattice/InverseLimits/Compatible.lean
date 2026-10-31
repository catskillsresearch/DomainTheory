module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeProjection

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

def Compatible (x : ∀ n, D n) : Prop := ∀ n, (P n).retr (x (n + 1)) = x n

end DomainTheory.ContinuousLattice
