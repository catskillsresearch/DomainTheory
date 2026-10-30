module

public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

noncomputable def inverseLimitSInfCoe (S : Set (InverseLimit D P)) : ∀ n, D n :=
  fun n => sInf ((fun x : InverseLimit D P => x.1 n) '' S)

end InverseLimit

end DomainTheory.ContinuousLattice
