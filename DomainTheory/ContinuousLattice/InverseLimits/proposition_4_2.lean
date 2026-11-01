module

public import DomainTheory.ContinuousLattice.InverseLimits.embInf
public import DomainTheory.ContinuousLattice.InverseLimits.limitProjectionToLevel

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

/-- Scott’s $i_{n\infty} : D_n \to D_\infty$ and $j_{\infty n} : D_\infty \to D_n$ as one
`ContinuousLatticeProjection`. -/
noncomputable def limitLevelProjection (n : ℕ) :
    ContinuousLatticeProjection (D n) (InverseLimit D P) where
  incl := embInf D P n
  retr := limitProjectionToLevel D P n
  retr_incl x := iComp.self D P n x
  incl_retr_le y := by
    rw [← Subtype.coe_le_coe]
    intro m
    exact iComp.incl_le D P n y m

/-- **Scott 1972, Proposition 4.2.** Each $j_{\infty n}$ is a projection (with inverse $i_{n\infty}$). -/
theorem proposition_4_2 (n : ℕ) :
    Nonempty (ContinuousLatticeProjection (D n) (InverseLimit D P)) :=
  ⟨limitLevelProjection D P n⟩

end InverseLimit

end DomainTheory.ContinuousLattice
