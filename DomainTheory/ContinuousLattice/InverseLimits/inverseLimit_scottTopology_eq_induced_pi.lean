/-ai
When every stage is a continuous lattice, the Scott topology on the inverse limit equals Scott's subspace inverse-limit topology, the topology inherited from the product of the stage Scott topologies.

Equip the inverse limit with that subspace topology and its T0 separation. The backward direction of Theorem 2.12, applied to injectivity of this space and to the agreement of its specialization order with the lattice order, yields the equality of the two topologies.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_t0Space
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_specializationLe_iff
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_isInjectiveSpace

public import DomainTheory.ContinuousLattice.Theorem212.IsContinuousLatticeu2eorderIso
public import DomainTheory.ContinuousLattice.Theorem212.theorem_2_12_backward_exact
@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))



















/-- The Scott lattice topology constructed on `D∞` agrees with Scott's literal inverse-limit
topology: the subspace topology inherited from the Pi product of the stage Scott topologies. -/
theorem inverseLimit_scottTopology_eq_induced_pi (hD : ∀ n, IsContinuousLattice (D n)) :
    (scottTopologicalSpace : TopologicalSpace (InverseLimit D P)) =
      inverseLimitTopology D P := by
  let : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  let : T0Space (InverseLimit D P) := inverseLimit_t0Space D P
  exact (theorem_2_12_backward_exact (inverseLimit_isInjectiveSpace D P hD)
    (inverseLimit_specializationLe_iff D P)).2

end InverseLimit
end DomainTheory.ContinuousLattice
