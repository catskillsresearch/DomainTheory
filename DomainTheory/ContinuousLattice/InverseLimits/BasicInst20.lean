module

public import DomainTheory.ContinuousLattice.InverseLimits.compatible_sInf
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

noncomputable instance : InfSet (InverseLimit D P) :=
  ⟨fun S => ⟨inverseLimitSInfCoe D P S, compatible_sInf D P S⟩⟩

end InverseLimit

end DomainTheory.ContinuousLattice
