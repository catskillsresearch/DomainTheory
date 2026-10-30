module

public import DomainTheory.ContinuousLattice.InverseLimits.instInfSet
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

noncomputable instance instCompleteLattice : CompleteLattice (InverseLimit D P) :=
  @completeLatticeOfInf (InverseLimit D P) (inverseLimitPartialOrder D P)
    inferInstance (isGLB_sInf' D P)

end InverseLimit

end DomainTheory.ContinuousLattice
