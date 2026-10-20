module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLT

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- The chosen strict inverse-limit order is `≤ ∧ ¬ ≥`. -/
theorem inverseLimitLT_iff_LE_not_GE (x y : InverseLimit D P) :
    inverseLimitLT D P x y ↔
      inverseLimitLE D P x y ∧ ¬ inverseLimitLE D P y x :=
  Iff.rfl

end InverseLimit

end DomainTheory.ContinuousLattice
