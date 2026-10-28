module

public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLT
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

instance inverseLimitPartialOrder : PartialOrder (InverseLimit D P) where
  le := inverseLimitLE D P
  lt := inverseLimitLT D P
  le_refl := inverseLimitLE.refl D P
  le_trans := inverseLimitLE.trans D P
  lt_iff_le_not_ge := inverseLimitLT.iff_LE_not_GE D P
  le_antisymm := inverseLimitLE.antisymm D P

end InverseLimit

end DomainTheory.ContinuousLattice
