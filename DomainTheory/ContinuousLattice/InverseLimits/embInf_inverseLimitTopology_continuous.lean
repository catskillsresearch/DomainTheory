/-ai
The stage embedding into the inverse limit is continuous from the Scott topology on the stage into Scott's subspace inverse-limit topology, the topology inherited from the product of the stages.

Once every stage is a continuous lattice, that subspace topology equals the Scott topology on the inverse limit, so continuity is the continuity of the Scott map.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_scottTopology_eq_induced_pi

public import DomainTheory.ContinuousLattice.Theorem212.IsContinuousLatticeu2eorderIso
@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))


/-- Proposition 4.2's embedding `i_{n∞}` is also continuous for Scott's literal inverse-limit
topology, namely the subspace topology inherited from the product `∏ₘ Dₘ`. -/
theorem embInf_inverseLimitTopology_continuous (hD : ∀ n, ContinuousLattice (D n)) (n : ℕ) :
    @Continuous (D n) (InverseLimit D P) scottTopologicalSpace
      (inverseLimitTopology D P) (embInf D P n) := by
  rw [← inverseLimit_scottTopology_eq_induced_pi D P hD]
  exact (embInf D P n).continuous

end InverseLimit
end DomainTheory.ContinuousLattice
