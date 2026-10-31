module

public import DomainTheory.ContinuousLattice.InverseLimits.Compatible

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

abbrev InverseLimit : Type u := {x : ∀ n, D n // Compatible D P x}

end DomainTheory.ContinuousLattice
