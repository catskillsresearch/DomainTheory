/-ai
If each component of a cocone equals the next component after the inclusion, then applying a later component after climbing the embeddings from level n returns the value of the component at level n.

The argument inducts along the inequality of levels. At the base, the embedding along a reflexivity is the identity. At a successor, the embedding is the inclusion after the embedding already reached, and the cocone equation replaces the next component by the current one.
ai-/
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


/-- Climbing then applying `f` is constant: `f_m(i_{m-1}…iₙ x) = fₙ(x)`. -/
theorem coconeInf_climb (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) {n : ℕ} (x : D n) :
    ∀ {m : ℕ} (h : n ≤ m), f m (embLE D P h x) = f n x := by
  intro m h
  induction m, h using Nat.le_induction with
  | base => rw [embLE_self]
  | succ k hk ih => rw [embLE_succ D P hk (Nat.le_succ_of_le hk), ← hf k, ih]

end InverseLimit
end DomainTheory.ContinuousLattice
