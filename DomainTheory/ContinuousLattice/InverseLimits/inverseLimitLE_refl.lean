/-ai
The coordinatewise order on compatible sequences is reflexive.

At every stage, the coordinate lies below itself.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- Reflexivity of the coordinatewise inverse-limit order. -/
theorem inverseLimitLE_refl (x : InverseLimit D P) :
    inverseLimitLE D P x x :=
  fun n => le_refl (x.1 n)

end InverseLimit

end DomainTheory.ContinuousLattice
