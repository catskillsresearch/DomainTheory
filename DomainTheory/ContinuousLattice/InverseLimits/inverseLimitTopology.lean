module

public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

@[reducible] noncomputable def inverseLimitTopology : TopologicalSpace (InverseLimit D P) :=
  TopologicalSpace.induced (Subtype.val : InverseLimit D P → ∀ n, D n)
    (@Pi.topologicalSpace ℕ D (fun _ => scottTopologicalSpace))

end InverseLimit

end DomainTheory.ContinuousLattice
