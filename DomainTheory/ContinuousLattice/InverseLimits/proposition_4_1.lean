module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.ContinuousLattices.theorem_2_12
public import DomainTheory.ContinuousLattice.ContinuousLattices.theorem_2_12_more
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitTopology
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

theorem proposition_4_1 (hD : ∀ n, ContinuousLattice (D n)) :
    ContinuousLattice (InverseLimit D P) := by
  let : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  let : T0Space (InverseLimit D P) := inverseLimit.t0Space D P
  exact (theorem_2_12.backward_exact (inverseLimit.isInjectiveSpace D P hD)
    (inverseLimit.specializationLe_iff D P)).1

end InverseLimit
end DomainTheory.ContinuousLattice
