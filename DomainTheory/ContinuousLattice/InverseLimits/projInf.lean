module

public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
public import DomainTheory.ContinuousLattice.InverseLimits.coe_sSup_of_directed
public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

def projInfFun (n : ℕ) (y : InverseLimit D P) : D n := y.1 n

namespace projInfFun

theorem preservesDirectedSup (n : ℕ) : PreservesDirectedSup (projInfFun D P n) := by
  intro S hS hSdir
  have hL : (sSup S : InverseLimit D P).1 n = sSup ((fun y : InverseLimit D P => y.1 n) '' S) := by
    rw [coe_sSup_of_directed D P S hS hSdir, sSup_apply_eq_sSup_image]
    congr 1
    rw [Set.image_image]
  exact hL

end projInfFun

noncomputable def projInf (n : ℕ) : ScottMap (InverseLimit D P) (D n) :=
  ⟨projInfFun D P n, continuous_of_preservesDirectedSup (projInfFun.preservesDirectedSup D P n)⟩

end InverseLimit

end DomainTheory.ContinuousLattice
