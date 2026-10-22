module

public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- The projection `j_{∞n} : D_∞ → Dₙ` as a bare function. -/
def projInfFun (n : ℕ) (y : InverseLimit D P) : D n := y.1 n

end InverseLimit

end DomainTheory.ContinuousLattice
