/-ai
Each coordinate of the climbing-and-descending sequence preserves directed suprema.

When n is at most m, that coordinate is the climb of the tower, which preserves directed suprema. When m is below n, that coordinate is the descent of the tower, which preserves directed suprema.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.BasicInst20
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.embLE
public import DomainTheory.ContinuousLattice.InverseLimits.projLE
public import DomainTheory.ContinuousLattice.InverseLimits.iComp
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_of_le
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_of_ge
public import DomainTheory.ContinuousLattice.InverseLimits.embLE_preservesDirectedSup
public import DomainTheory.ContinuousLattice.InverseLimits.projLE_preservesDirectedSup

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem iComp_preservesDirectedSup (n m : ℕ) :
    PreservesDirectedSup (fun x : D n => iComp D P n x m) := by
  by_cases h : n ≤ m
  · have hfun : (fun x : D n => iComp D P n x m) = embLE D P h :=
      funext (fun x => iComp_of_le D P h x)
    rw [hfun]; exact embLE_preservesDirectedSup D P h
  · have hfun : (fun x : D n => iComp D P n x m) = projLE D P (le_of_lt (not_le.mp h)) :=
      funext (fun x => iComp_of_ge D P h x)
    rw [hfun]; exact projLE_preservesDirectedSup D P _

end InverseLimit

end DomainTheory.ContinuousLattice
