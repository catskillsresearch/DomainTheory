/-ai
The projection from the inverse limit onto stage n is continuous from the subspace inverse-limit topology into the Scott topology of that stage. This is the coordinate continuity of the projection in Scott's Proposition 4.2.

The projection is the coordinate projection, which is continuous.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_coordinate_continuous

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))















































/-- Proposition 4.2's projection `j_{∞n}` is a continuous coordinate map for the explicit
product/subspace inverse-limit topology. -/
theorem projInf_inverseLimitTopology_continuous (n : ℕ) :
    @Continuous (InverseLimit D P) (D n) (inverseLimitTopology D P)
      scottTopologicalSpace (projInf D P n) :=
  inverseLimit_coordinate_continuous D P n

end InverseLimit
end DomainTheory.ContinuousLattice
