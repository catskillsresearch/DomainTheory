module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))























theorem embLE_mono {n m : ℕ} (h : n ≤ m) {x y : D n} (hxy : x ≤ y) :
    embLE D P h x ≤ embLE D P h y := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [embLE_self, embLE_self]
      exact hxy
  | succ k hk ih =>
      rw [embLE_succ D P hk (Nat.le_succ_of_le hk), embLE_succ D P hk (Nat.le_succ_of_le hk)]
      exact (P k).incl.monotone ih

end InverseLimit
end DomainTheory.ContinuousLattice
