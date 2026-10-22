module

public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.embInfFun
public import DomainTheory.ContinuousLattice.InverseLimits.embInf_preservesDirectedSup
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- The embedding `i_{n∞} : Dₙ → D_∞`, Scott-continuous. -/
noncomputable def embInf (n : ℕ) : ScottMap (D n) (InverseLimit D P) :=
  ⟨embInfFun D P n, continuous_of_preservesDirectedSup (embInf_preservesDirectedSup D P n)⟩

end InverseLimit

end DomainTheory.ContinuousLattice
