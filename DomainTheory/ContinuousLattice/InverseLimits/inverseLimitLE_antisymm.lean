/-ai
The coordinatewise order on compatible sequences is antisymmetric.

If each sequence lies below the other, then at every stage the two coordinates are equal, so the underlying functions agree and the sequences are equal.
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

/-- Antisymmetry of the coordinatewise inverse-limit order. -/
theorem inverseLimitLE_antisymm (x y : InverseLimit D P)
    (hxy : inverseLimitLE D P x y) (hyx : inverseLimitLE D P y x) :
    x = y :=
  Subtype.ext (funext fun n => le_antisymm (hxy n) (hyx n))

end InverseLimit

end DomainTheory.ContinuousLattice
