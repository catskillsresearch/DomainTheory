module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- Coordinatewise order on compatible sequences. Kept reducible so existing
subtype-order lemmas see the underlying pointwise relation definitionally. -/
abbrev inverseLimitLE (x y : InverseLimit D P) : Prop :=
  ∀ n,
    @LE.le (D n)
      (ChainCompletePartialOrder.instOfCompleteLattice
        (α := D n)).toPartialOrder.toPreorder.toLE
      (x.1 n) (y.1 n)

end InverseLimit

end DomainTheory.ContinuousLattice
