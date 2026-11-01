module

public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

/-- At index `n`, the infimum in `D n` of the `n`-th coordinates of `S`. -/
noncomputable def inverseLimitSInfCoe (S : Set (InverseLimit D P)) : ∀ n, D n :=
  fun n => sInf ((fun x : InverseLimit D P => x.1 n) '' S)

namespace inverseLimitSInfCoe

@[simp] theorem apply (S : Set (InverseLimit D P)) (n : ℕ) :
    inverseLimitSInfCoe D P S n = sInf ((fun x : InverseLimit D P => x.1 n) '' S) :=
  rfl

end inverseLimitSInfCoe

end InverseLimit

end DomainTheory.ContinuousLattice
