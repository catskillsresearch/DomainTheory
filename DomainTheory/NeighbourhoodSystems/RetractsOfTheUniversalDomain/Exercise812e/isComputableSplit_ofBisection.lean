module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.ComputableBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.posIdxFromBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.negIdxFromBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.primrec_posIdxFromBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.primrec_negIdxFromBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.splitFromBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.splitFromBisection_eq

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

/-- **`splitFromBisection` satisfies `IsComputableSplit`**, completing `8.12(e)(c)`. `posIdx`/
`negIdx` are literally `posIdxFromBisection`/`negIdxFromBisection`, unchanged from the original
design; the two (now-conditional, `Exercise812d.lean` `(d)(2)`) `_spec` fields case on
`splitFromBisection_eq`'s three branches — the first is immediately vacuous (`.1 = ∅` there,
contradicting `posIdx_spec`'s `≠ ∅` hypothesis, symmetrically for `negIdx_spec`'s second branch), the
other two unfold `posIdxFromBisection`/`negIdxFromBisection`'s own `selectFn` definition against the
same decider values. -/
noncomputable def isComputableSplit_ofBisection (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) :
    IsComputableSplit P Q (splitFromBisection P hDiff B hWnomin) where
  posIdx := posIdxFromBisection P hDiff B
  negIdx := negIdxFromBisection P hDiff B
  posIdx_primrec := primrec_posIdxFromBisection P hDiff B
  negIdx_primrec := primrec_negIdxFromBisection P hDiff B
  posIdx_spec n m k hne := by
    rw [splitFromBisection_eq P hDiff B hWnomin hpos hnomin hdiffClosed n m k] at hne ⊢
    split_ifs at hne ⊢ with h1 h2
    · exact absurd rfl hne
    · have h1' : emptyInterDec P (Nat.pair n k) = 0 := by
        have := emptyInterDec_le_one P (Nat.pair n k); omega
      simp [posIdxFromBisection, h1', h2]
    · have h1' : emptyInterDec P (Nat.pair n k) = 0 := by
        have := emptyInterDec_le_one P (Nat.pair n k); omega
      have h2' : emptyDiffDec P hDiff (Nat.pair n k) = 0 := by
        have := emptyDiffDec_le_one P hDiff (Nat.pair n k); omega
      simp [posIdxFromBisection, h1', h2']
  negIdx_spec n m k hne := by
    rw [splitFromBisection_eq P hDiff B hWnomin hpos hnomin hdiffClosed n m k] at hne ⊢
    split_ifs at hne ⊢ with h1 h2
    · simp [negIdxFromBisection, h1]
    · exact absurd rfl hne
    · have h1' : emptyInterDec P (Nat.pair n k) = 0 := by
        have := emptyInterDec_le_one P (Nat.pair n k); omega
      have h2' : emptyDiffDec P hDiff (Nat.pair n k) = 0 := by
        have := emptyDiffDec_le_one P hDiff (Nat.pair n k); omega
      simp [negIdxFromBisection, h1', h2']

end ComputableBisection

end DomainTheory.NeighbourhoodSystems
