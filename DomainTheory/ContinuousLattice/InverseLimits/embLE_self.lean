module

public import DomainTheory.ContinuousLattice.InverseLimits.embLE
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem embLE_self {n : ℕ} (h : n ≤ n) (x : D n) : embLE D P h x = x := by
  simp only [embLE, Nat.leRecOn_self]

end InverseLimit

end DomainTheory.ContinuousLattice
