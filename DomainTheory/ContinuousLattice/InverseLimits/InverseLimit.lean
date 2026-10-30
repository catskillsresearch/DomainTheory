module

public import DomainTheory.ContinuousLattice.InverseLimits.Compatible
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

abbrev InverseLimit : Type u := {x : ∀ n, D n // Compatible D P x}

end InverseLimit

end DomainTheory.ContinuousLattice
