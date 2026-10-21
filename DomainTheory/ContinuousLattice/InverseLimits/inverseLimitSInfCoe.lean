/-ai
The coordinatewise infimum of a set of compatible sequences, before the compatibility proof is packaged, is the function whose value at stage n is the infimum of the n-th coordinates of the members of the set.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- The coordinatewise infimum of a family of compatible sequences, before
packaging the compatibility proof. -/
noncomputable def inverseLimitSInfCoe (S : Set (InverseLimit D P)) : ∀ n, D n :=
  fun n => sInf ((fun x : InverseLimit D P => x.1 n) '' S)

end InverseLimit

end DomainTheory.ContinuousLattice
