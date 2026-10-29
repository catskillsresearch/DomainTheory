module
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup
public import Mathlib.Data.Set.Basic

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

def projLE {m n : ℕ} (h : m ≤ n) (x : D n) : D m :=
  Nat.leRecOn (C := fun k => D k → D m) h
    (fun {k} (g : D k → D m) (w : D (k + 1)) => g ((P k).retr w)) id x

namespace projLE

theorem self {m : ℕ} (h : m ≤ m) (x : D m) : projLE D P h x = x := by
  simp only [projLE, Nat.leRecOn_self, id_eq]

theorem succ {m n : ℕ} (h1 : m ≤ n) (h2 : m ≤ n + 1) (z : D (n + 1)) :
    projLE D P h2 z = projLE D P h1 ((P n).retr z) := by
  simp only [projLE]
  rw [Nat.leRecOn_succ (C := fun k => D k → D m) h1]

theorem mono {m n : ℕ} (h : m ≤ n) {x y : D n} (hxy : x ≤ y) :
    projLE D P h x ≤ projLE D P h y := by
  induction n, h using Nat.le_induction with
  | base =>
      rw [self, self]
      exact hxy
  | succ k hk ih =>
      rw [succ D P hk (Nat.le_succ_of_le hk), succ D P hk (Nat.le_succ_of_le hk)]
      exact ih ((P k).retr.monotone hxy)

theorem compatible {m : ℕ} (y : InverseLimit D P) :
    ∀ {n : ℕ} (h : m ≤ n), projLE D P h (y.1 n) = y.1 m := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => rw [self]
  | succ k hk ih => rw [succ D P hk (Nat.le_succ_of_le hk), y.2 k, ih]

theorem retr {m : ℕ} : ∀ {n : ℕ} (h : m + 1 ≤ n) (x : D n),
    (P m).retr (projLE D P h x) = projLE D P (Nat.le_of_succ_le h) x := by
  intro n h
  induction n, h using Nat.le_induction with
  | base =>
      intro x
      rw [succ D P (le_refl m) (Nat.le_of_succ_le (le_refl (m + 1))) x]
      simp only [self]
  | succ k hk ih =>
      intro x
      rw [succ D P hk (Nat.le_succ_of_le hk) x, ih ((P k).retr x),
        succ D P (Nat.le_of_succ_le hk) (Nat.le_of_succ_le (Nat.le_succ_of_le hk)) x]

theorem preservesDirectedSup {m n : ℕ} (h : m ≤ n) :
    PreservesDirectedSup (projLE D P h) := by
  induction n, h using Nat.le_induction with
  | base =>
      have hid : projLE D P (le_refl m) = id := funext (fun x => self D P (le_refl m) x)
      rw [hid]; intro S _ _; simp
  | succ k hk ih =>
      have hfun : projLE D P (Nat.le_succ_of_le hk)
          = projLE D P hk ∘ (fun z : D (k + 1) => (P k).retr z) :=
        funext (fun x => succ D P hk (Nat.le_succ_of_le hk) x)
      rw [hfun]
      exact ScottMap.preservesDirectedSup_comp ih
        (fun S hS hd => (P k).retr.preservesDirectedSup_coe S hS hd)

end projLE

end InverseLimit

end DomainTheory.ContinuousLattice
