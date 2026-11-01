module
public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeProjection

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

/-- At each index `n` of the tower, `(P n).incl` and `(P n).retr` form a Galois connection. -/
theorem tower_step_galoisConnection (n : ℕ) :
    GaloisConnection ((P n).incl : D n → D (n + 1)) ((P n).retr : D (n + 1) → D n) := by
  intro x y
  constructor
  · intro h
    have h' := (P n).retr.monotone h
    rwa [(P n).retr_incl] at h'
  · intro h
    exact le_trans ((P n).incl.monotone h) ((P n).incl_retr_le y)

end InverseLimit

end DomainTheory.ContinuousLattice
