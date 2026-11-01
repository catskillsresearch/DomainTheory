module

public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLT

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

/-- Coordinatewise order on `InverseLimit D P` from `inverseLimitLE` / `inverseLimitLT`. -/
instance inverseLimitPartialOrder : PartialOrder (InverseLimit D P) where
  le := inverseLimitLE D P
  lt := inverseLimitLT D P
  le_refl := inverseLimitLE.refl D P
  le_trans := inverseLimitLE.trans D P
  lt_iff_le_not_ge := inverseLimitLT.iff_LE_not_GE D P
  le_antisymm := inverseLimitLE.antisymm D P

end InverseLimit

end DomainTheory.ContinuousLattice
