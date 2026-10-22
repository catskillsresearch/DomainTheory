module

public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.iComp
public import DomainTheory.ContinuousLattice.InverseLimits.embLE_le
public import DomainTheory.ContinuousLattice.InverseLimits.projLE_compatible
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_of_ge
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_of_le
public import Mathlib.Data.Set.Basic

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
