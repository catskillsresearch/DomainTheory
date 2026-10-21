/-ai
When n is at most m, the m-th coordinate of the stage embedding of x is the climb of x up to stage m.

The defining split on the comparison of n and m takes the climb branch.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.BasicInst20
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.embLE
public import DomainTheory.ContinuousLattice.InverseLimits.iComp

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem iComp_of_le {n m : ℕ} (h : n ≤ m) (x : D n) : iComp D P n x m = embLE D P h x :=
  dite_eq_left h

end InverseLimit

end DomainTheory.ContinuousLattice
