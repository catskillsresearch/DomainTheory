module

public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

def embeddingAlongTower {n m : ℕ} (h : n ≤ m) (x : D n) : D m :=
  Nat.leRecOn h (fun {k} (y : D k) => (P k).incl y) x

namespace embeddingAlongTower

theorem self {n : ℕ} (h : n ≤ n) (x : D n) : embeddingAlongTower D P h x = x := by
  simp only [embeddingAlongTower, Nat.leRecOn_self]

theorem succ {n m : ℕ} (h1 : n ≤ m) (h2 : n ≤ m + 1) (x : D n) :
    embeddingAlongTower D P h2 x = (P m).incl (embeddingAlongTower D P h1 x) := by
  simp only [embeddingAlongTower]
  rw [Nat.leRecOn_succ h1]

theorem succ_left {n m : ℕ} (h1 : n ≤ m) (h2 : n + 1 ≤ m) (x : D n) :
    embeddingAlongTower D P h2 ((P n).incl x) = embeddingAlongTower D P h1 x := by
  simp only [embeddingAlongTower]
  exact Nat.leRecOn_succ_left x h1 h2

theorem le {n : ℕ} (y : InverseLimit D P) {m : ℕ} (h : n ≤ m) :
    embeddingAlongTower D P h (y.1 n) ≤ y.1 m := by
  induction m, h using Nat.le_induction with
  | base => exact le_of_eq (self D P _ _)
  | succ k hk ih =>
      rw [succ D P hk (Nat.le_succ_of_le hk)]
      calc (P k).incl (embeddingAlongTower D P hk (y.1 n))
          ≤ (P k).incl (y.1 k) := (P k).incl.monotone ih
        _ = (P k).incl ((P k).retr (y.1 (k + 1))) := by rw [y.2 k]
        _ ≤ y.1 (k + 1) := (P k).incl_retr_le _

theorem mono {n m : ℕ} (h : n ≤ m) {x y : D n} (hxy : x ≤ y) :
    embeddingAlongTower D P h x ≤ embeddingAlongTower D P h y := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [self, self]
      exact hxy
  | succ k hk ih =>
      rw [succ D P hk (Nat.le_succ_of_le hk), succ D P hk (Nat.le_succ_of_le hk)]
      exact (P k).incl.monotone ih

theorem preservesDirectedSup {n m : ℕ} (h : n ≤ m) :
    PreservesDirectedSup (embeddingAlongTower D P h) := by
  induction m, h using Nat.le_induction with
  | base =>
      have hid : embeddingAlongTower D P (le_refl n) = id :=
        funext (fun x => self D P (le_refl n) x)
      rw [hid]; intro S _ _; simp
  | succ k hk ih =>
      have hfun : embeddingAlongTower D P (Nat.le_succ_of_le hk)
          = (fun y : D k => (P k).incl y) ∘ embeddingAlongTower D P hk :=
        funext (fun x => succ D P hk (Nat.le_succ_of_le hk) x)
      rw [hfun]
      exact ScottMap.preservesDirectedSup_comp
        (fun S hS hd => (P k).incl.preservesDirectedSup_coe S hS hd) ih

end embeddingAlongTower

end InverseLimit

end DomainTheory.ContinuousLattice
