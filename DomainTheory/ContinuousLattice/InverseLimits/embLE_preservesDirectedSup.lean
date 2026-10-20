module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.BasicInst20
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.embLE
public import DomainTheory.ContinuousLattice.InverseLimits.embLE_self
public import DomainTheory.ContinuousLattice.InverseLimits.embLE_succ

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- The tower of embeddings is Scott-continuous (a composite of the `iₖ`). -/
theorem embLE_preservesDirectedSup {n m : ℕ} (h : n ≤ m) :
    PreservesDirectedSup (embLE D P h) := by
  induction m, h using Nat.le_induction with
  | base =>
      have hid : embLE D P (le_refl n) = id := funext (fun x => embLE_self D P (le_refl n) x)
      rw [hid]; intro S _ _; simp
  | succ k hk ih =>
      have hfun : embLE D P (Nat.le_succ_of_le hk)
          = (fun y : D k => (P k).incl y) ∘ embLE D P hk :=
        funext (fun x => embLE_succ D P hk (Nat.le_succ_of_le hk) x)
      rw [hfun]
      exact ScottMap.preservesDirectedSup_comp
        (fun S hS hd => (P k).incl.preservesDirectedSup_coe S hS hd) ih

end InverseLimit

end DomainTheory.ContinuousLattice
