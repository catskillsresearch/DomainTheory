/-ai
For a compatible sequence x, the stage embeddings of its coordinates are monotone: the embedding of the n-th coordinate lies below the embedding of the next coordinate.

The recursion equation rewrites the earlier embedding as the later embedding of the inclusion of x_n. Monotonicity of that later embedding applies once the inclusion of x_n lies below x at stage n+1. Compatibility replaces the inclusion of x_n by the inclusion of the retraction of x at stage n+1, and an inclusion after a retraction lies below the identity.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.embInf_succ

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))


/-- The family `n ↦ i_{n∞}(xₙ)` is monotone (the lub defining `x` is monotone). -/
theorem embInf_le_succ (x : InverseLimit D P) (n : ℕ) :
    embInf D P n (x.1 n) ≤ embInf D P (n + 1) (x.1 (n + 1)) := by
  rw [← embInf_succ D P n (x.1 n)]
  exact embInf_monotone D P (n + 1)
    (by calc (P n).incl (x.1 n) = (P n).incl ((P n).retr (x.1 (n + 1))) := by rw [x.2 n]
          _ ≤ x.1 (n + 1) := (P n).incl_retr_le _)

end InverseLimit
end DomainTheory.ContinuousLattice
