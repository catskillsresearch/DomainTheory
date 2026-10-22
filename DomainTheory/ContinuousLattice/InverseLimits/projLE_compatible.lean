/-ai
For a compatible sequence y and m at most n, descending the n-th coordinate down to level m recovers the m-th coordinate.

The argument is by induction along m at most n. At the base, descent is the identity. At a successor, one retraction is peeled off and compatibility of y supplies the inductive step.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.BasicInst20
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.projLE
public import DomainTheory.ContinuousLattice.InverseLimits.projLE_self
public import DomainTheory.ContinuousLattice.InverseLimits.projLE_succ

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- For a compatible sequence `y`, descending from level `n` to `m ≤ n` recovers `yₘ`. -/
theorem projLE_compatible {m : ℕ} (y : InverseLimit D P) :
    ∀ {n : ℕ} (h : m ≤ n), projLE D P h (y.1 n) = y.1 m := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => rw [projLE_self]
  | succ k hk ih => rw [projLE_succ D P hk (Nat.le_succ_of_le hk), y.2 k, ih]

end InverseLimit

end DomainTheory.ContinuousLattice
