module

public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE
public import Mathlib.Data.Set.Basic

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

namespace inverseLimitLT

/-- The chosen strict inverse-limit order is `≤ ∧ ¬ ≥`. -/
theorem iff_LE_not_GE (x y : InverseLimit D P) :
    inverseLimitLT D P x y ↔
      inverseLimitLE D P x y ∧ ¬ inverseLimitLE D P y x :=
  Iff.rfl

end inverseLimitLT

end InverseLimit

end DomainTheory.ContinuousLattice
