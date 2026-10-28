module
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem projection_galoisConnection (n : ℕ) :
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
