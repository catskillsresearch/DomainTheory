module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.BasicInst20
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.embLE
public import DomainTheory.ContinuousLattice.InverseLimits.projLE

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- Scott's embedding component `i_{n∞}(x)_m`: climb for `m ≥ n`, descend for `m < n`. -/
def iComp (n : ℕ) (x : D n) (m : ℕ) : D m :=
  if h : n ≤ m then embLE D P h x else projLE D P (le_of_lt (not_le.mp h)) x

end InverseLimit

end DomainTheory.ContinuousLattice
