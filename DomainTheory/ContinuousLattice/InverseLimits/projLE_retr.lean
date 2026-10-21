/-ai
Peeling the retraction at stage m off a descent from a stage n at least m+1 equals the descent from that same stage down to m.

The argument is by induction along m+1 at most n. At the base, one retraction peels off and the remaining descent is the identity. At a successor, the outer retraction peels off, the inductive hypothesis applies to the retracted element, and one further successor step reassembles the shorter descent.
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

/-- Peeling the last projection: `(P m).retr ∘ projLE (m+1 ≤ n) = projLE (m ≤ n)`. -/
theorem projLE_retr {m : ℕ} : ∀ {n : ℕ} (h : m + 1 ≤ n) (x : D n),
    (P m).retr (projLE D P h x) = projLE D P (Nat.le_of_succ_le h) x := by
  intro n h
  induction n, h using Nat.le_induction with
  | base =>
      intro x
      rw [projLE_succ D P (le_refl m) (Nat.le_of_succ_le (le_refl (m + 1))) x]
      simp only [projLE_self]
  | succ k hk ih =>
      intro x
      rw [projLE_succ D P hk (Nat.le_succ_of_le hk) x, ih ((P k).retr x),
        projLE_succ D P (Nat.le_of_succ_le hk) (Nat.le_of_succ_le (Nat.le_succ_of_le hk)) x]

end InverseLimit

end DomainTheory.ContinuousLattice
