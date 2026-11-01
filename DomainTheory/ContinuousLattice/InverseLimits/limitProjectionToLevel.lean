module

public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice
import DomainTheory.ContinuousLattice.InverseLimits.coe_sSup_of_directed

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

def limitProjectionToLevel.fun (n : ℕ) (y : InverseLimit D P) : D n := y.1 n

namespace limitProjectionToLevel

theorem preservesDirectedSup (n : ℕ) : PreservesDirectedSup (limitProjectionToLevel.fun D P n) := by
  intro S hS hSdir
  have hL : (sSup S : InverseLimit D P).1 n = sSup ((fun y : InverseLimit D P => y.1 n) '' S) := by
    rw [coe_sSup_of_directed D P S hS hSdir, sSup_apply_eq_sSup_image]
    congr 1
    rw [Set.image_image]
  exact hL

end limitProjectionToLevel

noncomputable def limitProjectionToLevel (n : ℕ) : ScottMap (InverseLimit D P) (D n) :=
  ⟨limitProjectionToLevel.fun D P n,
    PreservesDirectedSup.continuous_of (limitProjectionToLevel.preservesDirectedSup D P n)⟩

end InverseLimit

end DomainTheory.ContinuousLattice
