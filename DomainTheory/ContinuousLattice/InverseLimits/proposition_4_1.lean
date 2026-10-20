module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_t0Space
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_specializationLe_iff
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_isInjectiveSpace

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))



















/-- **Scott 1972, Proposition 4.1.** The inverse limit is injective by the coordinatewise
Proposition 3.8/Lemma 3.9 construction; Theorem 2.12 then gives the continuous-lattice structure
on the existing componentwise complete lattice. -/
theorem proposition_4_1 (hD : ∀ n, IsContinuousLattice (D n)) :
    IsContinuousLattice (InverseLimit D P) := by
  let : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  let : T0Space (InverseLimit D P) := inverseLimit_t0Space D P
  exact (theorem_2_12_backward_exact (inverseLimit_isInjectiveSpace D P hD)
    (inverseLimit_specializationLe_iff D P)).1

end InverseLimit
end DomainTheory.ContinuousLattice
