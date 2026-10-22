/-ai
The stage embedding of the n-th coordinate of a compatible sequence y lies below y at every coordinate.

When the coordinate m is at least n, the component climbs and climbing a coordinate of y stays below the later coordinate. When m is below n, the component descends, and descending a compatible sequence recovers the earlier coordinate.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.BasicInst20
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.iComp
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_of_le
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_of_ge
public import DomainTheory.ContinuousLattice.InverseLimits.projLE_compatible
public import DomainTheory.ContinuousLattice.InverseLimits.embLE_le

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- `i_{n∞}(yₙ) ⊑ y` coordinatewise (the heart of `incl_retr_le` for `j_{∞n}`). -/
theorem iComp_incl_le (n : ℕ) (y : InverseLimit D P) (m : ℕ) :
    iComp D P n (y.1 n) m ≤ y.1 m := by
  by_cases h : n ≤ m
  · rw [iComp_of_le D P h]; exact embLE_le D P y h
  · rw [iComp_of_ge D P h]
    exact le_of_eq (projLE_compatible D P y (le_of_lt (not_le.mp h)))

end InverseLimit

end DomainTheory.ContinuousLattice
