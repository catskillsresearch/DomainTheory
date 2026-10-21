/-ai
The mediating map of a cocone is continuous from the inverse-limit topology into the Scott topology of the codomain, whenever each level is a continuous lattice.

The inverse-limit topology agrees with the Scott topology of the inverse limit, and the mediating map preserves directed suprema, so it is continuous for that Scott topology.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimit_scottTopology_eq_induced_pi
public import DomainTheory.ContinuousLattice.InverseLimits.coconeInf_preservesDirectedSup

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

















































variable {D' : Type*} [CompleteLattice D']


/-- Corollary 4.3's formula `f∞(x) = ⨆ₙ fₙ(xₙ)` is continuous not only for the reconstructed Scott
topology on `D∞`, but explicitly for Scott's product/subspace inverse-limit topology. -/
theorem coconeInf_inverseLimitTopology_continuous (hD : ∀ n, IsContinuousLattice (D n))
    (f : ∀ n, ScottMap (D n) D') :
    @Continuous (InverseLimit D P) D' (inverseLimitTopology D P)
      scottTopologicalSpace (coconeInf D P f) := by
  rw [← inverseLimit_scottTopology_eq_induced_pi D P hD]
  exact continuous_of_preservesDirectedSup (coconeInf_preservesDirectedSup D P f)

end InverseLimit
end DomainTheory.ContinuousLattice
