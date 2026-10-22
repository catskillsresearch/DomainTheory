module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.ComputableBisection

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

section Congr

variable {n n' k k' m m' : ℕ}

/-- `emptyDiffDec` is a well-defined function of the two *sets* `P.X n`, `P.X k`: it does not
distinguish between different raw indices presenting the same set. Needs `V.DiffClosed`, not just
`IsComputableDiff P` — a hypothesis gap found while scoping `(e)(c)` (2026-07-05), absent from
`(e)(c)`'s original draft signature. -/
theorem emptyDiffDec_congr (hdiffClosed : V.DiffClosed) (hnomin : V.NoMinimal)
    (hn : P.X n = P.X n') (hk : P.X k = P.X k') :
    emptyDiffDec P hDiff (Nat.pair n k) = emptyDiffDec P hDiff (Nat.pair n' k') := by
  have h1 := emptyDiffDec_eq_one_iff P hDiff hdiffClosed hnomin n k
  have h2 := emptyDiffDec_eq_one_iff P hDiff hdiffClosed hnomin n' k'
  rw [hn, hk] at h1
  have hiff : emptyDiffDec P hDiff (Nat.pair n k) = 1 ↔ emptyDiffDec P hDiff (Nat.pair n' k') = 1 :=
    h1.trans h2.symm
  have hle1 := emptyDiffDec_le_one P hDiff (Nat.pair n k)
  have hle2 := emptyDiffDec_le_one P hDiff (Nat.pair n' k')
  omega

end Congr

end ComputableBisection

end DomainTheory.NeighbourhoodSystems
