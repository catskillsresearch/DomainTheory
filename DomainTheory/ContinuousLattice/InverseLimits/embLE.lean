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

/-- Climb the tower of embeddings: for `n ≤ m`, `embLE h = i_{m-1} ∘ … ∘ iₙ : Dₙ → D_m`. -/
def embLE {n m : ℕ} (h : n ≤ m) (x : D n) : D m :=
  Nat.leRecOn h (fun {k} (y : D k) => (P k).incl y) x

end InverseLimit

end DomainTheory.ContinuousLattice
