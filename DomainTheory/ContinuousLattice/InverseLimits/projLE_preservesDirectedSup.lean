/-ai
Descending the tower of retractions from stage n down to stage m preserves directed suprema, as a composite of the stage retractions.

The argument is by induction along m at most n. At the base, descent is the identity, which preserves directed suprema. At a successor, descent one stage further is the descent already constructed composed with the next retraction, and preservation of directed suprema passes through that composite.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
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

/-- The tower of projections is Scott-continuous (a composite of the `jₖ`). -/
theorem projLE_preservesDirectedSup {m n : ℕ} (h : m ≤ n) :
    PreservesDirectedSup (projLE D P h) := by
  induction n, h using Nat.le_induction with
  | base =>
      have hid : projLE D P (le_refl m) = id := funext (fun x => projLE_self D P (le_refl m) x)
      rw [hid]; intro S _ _; simp
  | succ k hk ih =>
      have hfun : projLE D P (Nat.le_succ_of_le hk)
          = projLE D P hk ∘ (fun z : D (k + 1) => (P k).retr z) :=
        funext (fun x => projLE_succ D P hk (Nat.le_succ_of_le hk) x)
      rw [hfun]
      exact ScottMap.preservesDirectedSup_comp ih
        (fun S hS hd => (P k).retr.preservesDirectedSup_coe S hS hd)

end InverseLimit

end DomainTheory.ContinuousLattice
