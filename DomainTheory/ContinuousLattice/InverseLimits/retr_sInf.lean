module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.projection_galoisConnection
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- `jₙ` preserves arbitrary infima (it is the upper adjoint of `iₙ`). -/
theorem retr_sInf (n : ℕ) (A : Set (D (n + 1))) :
    (P n).retr (sInf A) = sInf ((P n).retr '' A) := by
  rw [(projection_galoisConnection D P n).u_sInf, sInf_image]

end InverseLimit

end DomainTheory.ContinuousLattice
