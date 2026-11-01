module

public import DomainTheory.ContinuousLattice.InverseLimits.instInfSet

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

/-- **Scott 1972, §4.** Complete lattice structure on compatible sequences. -/
noncomputable instance instCompleteLattice : CompleteLattice (InverseLimit D P) :=
  @completeLatticeOfInf (InverseLimit D P) (inverseLimitPartialOrder D P)
    inferInstance (instInfSet.isGLB_sInf' D P)

end InverseLimit

end DomainTheory.ContinuousLattice
