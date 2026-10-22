module

public import DomainTheory.ContinuousLattice.InverseLimits.Compatible
public import DomainTheory.ContinuousLattice.InverseLimits.iComp
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_of_ge
public import DomainTheory.ContinuousLattice.InverseLimits.iComp_of_le
public import DomainTheory.ContinuousLattice.InverseLimits.projLE_retr
public import DomainTheory.ContinuousLattice.InverseLimits.projLE_succ
public import DomainTheory.ContinuousLattice.InverseLimits.projLE_self
public import DomainTheory.ContinuousLattice.InverseLimits.embLE_succ
public import DomainTheory.ContinuousLattice.InverseLimits.embLE_self
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- The sequence `i_{n∞}(x)` is compatible, hence a genuine point of `D_∞`. -/
theorem iComp_compatible (n : ℕ) (x : D n) : Compatible D P (iComp D P n x) := by
  intro m
  by_cases h1 : n ≤ m
  · rw [iComp_of_le D P h1, iComp_of_le D P (Nat.le_succ_of_le h1),
      embLE_succ D P h1 (Nat.le_succ_of_le h1), (P m).retr_incl]
  · by_cases h2 : n ≤ m + 1
    · have hn : n = m + 1 := le_antisymm h2 (not_le.mp h1)
      subst hn
      rw [iComp_of_le D P (le_refl (m + 1)), embLE_self, iComp_of_ge D P h1,
        projLE_succ D P (le_refl m) (le_of_lt (not_le.mp h1)) x, projLE_self]
    · rw [iComp_of_ge D P h2, iComp_of_ge D P h1,
        projLE_retr D P (le_of_lt (not_le.mp h2)) x]

end InverseLimit

end DomainTheory.ContinuousLattice
