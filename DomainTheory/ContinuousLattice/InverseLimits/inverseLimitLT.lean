module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- Strict coordinatewise order induced by `inverseLimitLE`. -/
abbrev inverseLimitLT (x y : InverseLimit D P) : Prop :=
  inverseLimitLE D P x y ∧ ¬ inverseLimitLE D P y x

end InverseLimit

end DomainTheory.ContinuousLattice
