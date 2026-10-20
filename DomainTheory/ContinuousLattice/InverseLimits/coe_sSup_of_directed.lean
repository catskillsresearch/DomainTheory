module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Compatible
public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitPartialOrder
public import DomainTheory.ContinuousLattice.InverseLimits.BasicInst20
public import DomainTheory.ContinuousLattice.InverseLimits.instCompleteLattice

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- For a directed, nonempty family, the inverse-limit supremum is computed pointwise (each `jₙ`
is Scott-continuous, so the pointwise sup of compatible sequences is compatible and is the least
upper bound in `D_∞`). -/
theorem coe_sSup_of_directed (S : Set (InverseLimit D P)) (hSne : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) :
    ((sSup S : InverseLimit D P) : ∀ n, D n) = sSup (Subtype.val '' S) := by
  have hcompat : Compatible D P (sSup (Subtype.val '' S)) := by
    intro n
    rw [sSup_apply_eq_sSup_image, sSup_apply_eq_sSup_image]
    set A : Set (D (n + 1)) := (fun f : ∀ m, D m => f (n + 1)) '' (Subtype.val '' S) with hA
    have hAne : A.Nonempty := (hSne.image _).image _
    have hAdir : DirectedOn (· ≤ ·) A := by
      rintro _ ⟨_, ⟨x, hxS, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hyS, rfl⟩, rfl⟩
      obtain ⟨z, hzS, hxz, hyz⟩ := hSdir x hxS y hyS
      exact ⟨z.1 (n + 1), ⟨z.1, ⟨z, hzS, rfl⟩, rfl⟩, hxz (n + 1), hyz (n + 1)⟩
    rw [(P n).retr.preservesDirectedSup_coe A hAne hAdir]
    congr 1
    rw [hA, Set.image_image]
    exact Set.image_congr (by rintro _ ⟨x, _, rfl⟩; exact x.2 n)
  set p : InverseLimit D P := ⟨sSup (Subtype.val '' S), hcompat⟩ with hp
  have hlub : IsLUB S p := by
    constructor
    · intro x hx
      refine Subtype.coe_le_coe.mp ?_
      exact le_sSup (Set.mem_image_of_mem _ hx)
    · intro b hb
      refine Subtype.coe_le_coe.mp ?_
      refine sSup_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact Subtype.coe_le_coe.mpr (hb hx)
  rw [(isLUB_sSup S).unique hlub]

end InverseLimit

end DomainTheory.ContinuousLattice
