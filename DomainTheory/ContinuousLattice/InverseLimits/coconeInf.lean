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

variable {D' : Type*} [CompleteLattice D']

/-- The mediating map of Corollary 4.3: `f∞(x) = ⨆ₙ fₙ(xₙ)`. -/
def coconeInf (f : ∀ n, ScottMap (D n) D') (x : InverseLimit D P) : D' :=
  ⨆ n, f n (x.1 n)

end InverseLimit

end DomainTheory.ContinuousLattice
