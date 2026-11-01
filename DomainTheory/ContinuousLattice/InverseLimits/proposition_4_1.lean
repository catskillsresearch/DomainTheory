module

public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
import DomainTheory.ContinuousLattice.ContinuousLattices.continuousLattice_scottTopology_of_injective
import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitTopology

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

theorem proposition_4_1 (hD : ∀ n, ContinuousLattice (D n)) :
    ContinuousLattice (InverseLimit D P) := by
  let : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  let : T0Space (InverseLimit D P) := inverseLimit.t0Space D P
  exact (continuousLattice_scottTopology_of_injective (inverseLimit.isInjectiveSpace D P hD)
    (inverseLimit.specializationPreorder_iff D P)).1

end InverseLimit
end DomainTheory.ContinuousLattice
