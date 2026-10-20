module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.BasicInst20
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- Descend the tower of projections: for `m ≤ n`, `projLE h = j_m ∘ … ∘ j_{n-1} : D_n → Dₘ`. -/
def projLE {m n : ℕ} (h : m ≤ n) (x : D n) : D m :=
  Nat.leRecOn (C := fun k => D k → D m) h
    (fun {k} (g : D k → D m) (w : D (k + 1)) => g ((P k).retr w)) id x

end InverseLimit

end DomainTheory.ContinuousLattice
