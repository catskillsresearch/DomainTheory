/-ai
The pointwise infimum of a set of compatible sequences is compatible.

At each level the projection preserves the infimum of the next coordinates. Compatibility of each sequence identifies those next coordinates with the current coordinates, so the projected infimum equals the infimum of the current coordinates.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Compatible
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.retr_sInf
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitSInfCoe

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- The pointwise infimum of compatible sequences is compatible. -/
theorem compatible_sInf (S : Set (InverseLimit D P)) :
    Compatible D P (inverseLimitSInfCoe D P S) := by
  intro n
  rw [inverseLimitSInfCoe, inverseLimitSInfCoe, retr_sInf]
  congr 1
  rw [Set.image_image]
  exact Set.image_congr (by rintro x hx; exact x.2 n)

end InverseLimit

end DomainTheory.ContinuousLattice
