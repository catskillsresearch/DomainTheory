/-ai
The coordinatewise order on compatible sequences is transitive.

At every stage, the coordinate inequality is transitive.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- Transitivity of the coordinatewise inverse-limit order. -/
theorem inverseLimitLE_trans (x y z : InverseLimit D P)
    (hxy : inverseLimitLE D P x y) (hyz : inverseLimitLE D P y z) :
    inverseLimitLE D P x z :=
  fun n => le_trans (hxy n) (hyz n)

end InverseLimit

end DomainTheory.ContinuousLattice
