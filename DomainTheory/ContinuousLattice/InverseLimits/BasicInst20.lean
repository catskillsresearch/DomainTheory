module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitSInfCoe
public import DomainTheory.ContinuousLattice.InverseLimits.compatible_sInf

@[expose] public section

set_option linter.unusedSectionVars false

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
