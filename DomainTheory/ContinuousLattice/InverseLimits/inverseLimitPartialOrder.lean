/-ai
The inverse limit carries the coordinatewise partial order inherited from the product of the stages. The order and the strict order are the coordinatewise relations, and reflexivity, transitivity, the characterization of the strict order, and antisymmetry are the corresponding properties of those relations.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLT
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE_refl
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE_trans
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLE_antisymm
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitLT_iff_LE_not_GE

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- The inverse limit carries the coordinatewise order inherited from its
ambient product. This declaration makes that order explicit instead of
leaving typeclass search to choose an equivalent route. -/
instance inverseLimitPartialOrder : PartialOrder (InverseLimit D P) where
  le := inverseLimitLE D P
  lt := inverseLimitLT D P
  le_refl := inverseLimitLE_refl D P
  le_trans := inverseLimitLE_trans D P
  lt_iff_le_not_ge := inverseLimitLT_iff_LE_not_GE D P
  le_antisymm := inverseLimitLE_antisymm D P

end InverseLimit

end DomainTheory.ContinuousLattice
