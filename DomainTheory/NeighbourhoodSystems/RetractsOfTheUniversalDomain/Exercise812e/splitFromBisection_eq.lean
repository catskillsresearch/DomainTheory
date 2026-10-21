/-ai
On a presented triple, the bisection split is the empty set paired with the target neighbourhood when the intersection decider fires, the target neighbourhood paired with the empty set when the difference decider fires, and the two bisection halves otherwise.

The given indices are themselves a presentation witness. Congruence identifies the chosen witness's deciders with the given ones. The two firing branches are then immediate, and the silent branch rewrites the chosen halves by the bisection congruences.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.ComputableBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.emptyInterDec_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.emptyDiffDec_congr
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.splitFromBisection

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

/-- **`splitFromBisection`, unfolded at a literal presented triple `(P.X n, Q.X m, P.X k)`**,
bridging `Classical.choose`'s own (possibly different) witness back to the literal `n, m, k` given,
via `(e)(c)(i)`'s `emptyInterDec_congr`/`emptyDiffDec_congr` (for the two decider branches) and
`B.left_congr`/`B.right_congr` (for the bisection branch). The one lemma both `posIdx_spec`/
`negIdx_spec` and `splitFromBisection_isSplitSpec'` are built from. -/
theorem splitFromBisection_eq (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) (n m k : ℕ) :
    splitFromBisection P hDiff B hWnomin (P.X n) (Q.X m) (P.X k) =
      if emptyInterDec P (Nat.pair n k) = 1 then (∅, Q.X m)
      else if emptyDiffDec P hDiff (Nat.pair n k) = 1 then (Q.X m, ∅)
      else (Q.X (B.left m), Q.X (B.right m)) := by
  have hex : ∃ n' m' k', P.X n = P.X n' ∧ Q.X m = Q.X m' ∧ P.X k = P.X k' :=
    ⟨n, m, k, rfl, rfl, rfl⟩
  obtain ⟨hn', hm', hk'⟩ := hex.choose_spec.choose_spec.choose_spec
  have hInterEq : emptyInterDec P (Nat.pair hex.choose hex.choose_spec.choose_spec.choose) =
      emptyInterDec P (Nat.pair n k) := (emptyInterDec_congr P hpos hnomin hn' hk').symm
  have hDiffEq : emptyDiffDec P hDiff (Nat.pair hex.choose hex.choose_spec.choose_spec.choose) =
      emptyDiffDec P hDiff (Nat.pair n k) :=
    (emptyDiffDec_congr P hDiff hdiffClosed hnomin hn' hk').symm
  unfold splitFromBisection
  rw [dite_eq_left hex, hInterEq, hDiffEq]
  split_ifs with h1 h2
  · rfl
  · rfl
  · have hl := (B.left_congr m hex.choose_spec.choose hm').symm
    have hr := (B.right_congr m hex.choose_spec.choose hm').symm
    rw [hl, hr]

end ComputableBisection

end DomainTheory.NeighbourhoodSystems
