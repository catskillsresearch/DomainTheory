module

public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitTopology
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.ContinuousLattices.theorem_2_12_backward_exact
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_isInjectiveSpace
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_specializationLe_iff
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_t0Space
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import Mathlib.Data.Set.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))


/-- The Scott lattice topology constructed on `D∞` agrees with Scott's literal inverse-limit
topology: the subspace topology inherited from the Pi product of the stage Scott topologies. -/
theorem inverseLimit_scottTopology_eq_induced_pi (hD : ∀ n, ContinuousLattice (D n)) :
    (scottTopologicalSpace : TopologicalSpace (InverseLimit D P)) =
      inverseLimitTopology D P := by
  let : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  let : T0Space (InverseLimit D P) := inverseLimit_t0Space D P
  exact (theorem_2_12_backward_exact (inverseLimit_isInjectiveSpace D P hD)
    (inverseLimit_specializationLe_iff D P)).2

end InverseLimit
end DomainTheory.ContinuousLattice
