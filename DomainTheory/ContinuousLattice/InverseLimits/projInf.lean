module

public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.projInfFun
public import DomainTheory.ContinuousLattice.InverseLimits.eval_preservesDirectedSup
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- The projection `j_{∞n} : D_∞ → Dₙ`, Scott-continuous. -/
noncomputable def projInf (n : ℕ) : ScottMap (InverseLimit D P) (D n) :=
  ⟨projInfFun D P n, continuous_of_preservesDirectedSup (eval_preservesDirectedSup D P n)⟩

end InverseLimit

end DomainTheory.ContinuousLattice
