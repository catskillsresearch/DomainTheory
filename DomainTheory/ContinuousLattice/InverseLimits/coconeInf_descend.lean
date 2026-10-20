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

















































variable {D' : Type*} [CompleteLattice D']


/-- Descending then applying `f` only decreases: `f_m(j_m…j_{n-1} x) ⊑ fₙ(x)`. -/
theorem coconeInf_descend (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) {m : ℕ} :
    ∀ {n : ℕ} (h : m ≤ n) (x : D n), f m (projLE D P h x) ≤ f n x := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => intro x; exact le_of_eq (congrArg (f m) (projLE_self D P (le_refl m) x))
  | succ k hk ih =>
      intro x
      rw [projLE_succ D P hk (Nat.le_succ_of_le hk)]
      calc f m (projLE D P hk ((P k).retr x)) ≤ f k ((P k).retr x) := ih ((P k).retr x)
        _ = f (k + 1) ((P k).incl ((P k).retr x)) := hf k _
        _ ≤ f (k + 1) x := (f (k + 1)).monotone ((P k).incl_retr_le x)

end InverseLimit
end DomainTheory.ContinuousLattice
