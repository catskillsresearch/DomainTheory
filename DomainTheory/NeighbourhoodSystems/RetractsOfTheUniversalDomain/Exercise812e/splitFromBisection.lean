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

open scoped Classical in
/-- **The classical split, built from a `ComputableBisection`**: fall back to the prober-side
deciders (`(d)(2)`'s `emptyInterDec`/`emptyDiffDec`) whenever the input triple presents as `(P.X n,
Q.X m, P.X k)` for some indices, and to the abstract choice-based `splitChoice'` (`Exercise812c.lean`)
otherwise. **Redesigned 2026-07-06 (repairing `8.12(g)(3)`)**: the *original* design (below, kept for
the record) always returned `(Q.X (posIdxFromBisection …), Q.X (negIdxFromBisection …))` — literally
never `∅` — on the presented branch, which is jointly unsatisfiable with `SplitSpec'` (see
`Exercise812d.lean`'s `IsComputableSplit.posIdx_spec` docstring for the full argument). The fix:
route the *set-level* value through the same two deciders `posIdxFromBisection`/
`negIdxFromBisection` already consult, but let the two "one decider fires" branches produce the
literal `∅`/`B'` pair directly (matching what `SplitSpec'` demands: `A ∩ Xn = ∅` forces `.1 = ∅` and
gives `.2` all of `B'`, symmetrically for `A \ Xn = ∅`), only falling through to the genuine
bisection (`B.left`/`B.right`) when *neither* decider fires (the case `exists_split'` itself needs
`E.NoMinimal` to bisect `B'` into two nonempty halves). `posIdxFromBisection`/`negIdxFromBisection`
themselves need **no** change: they already compute exactly the right *index* in the "genuinely
nonempty" branch of each field and an unread junk placeholder (`m`) in the "should be `∅`" branch —
the bug was purely in `splitFromBisection` wrapping *both* branches in `Q.X (⋯)`, which can never
literally be `∅`. Also generalizes the previous "not presented → junk `(B', B')`" fallback (wrong in
general — `.1 ∩ .2 = B' ∩ B' = B'`, not `∅`, unless `B' = ∅`) to the always-correct `splitChoice'`,
needed for `SplitSpec'` to hold on *every* `A`/`Xn`, not just presented ones (`(e)(c)`'s own
`posIdx_spec`/`negIdx_spec` only ever constrain the presented case, so this choice of fallback is
free to fix without touching `IsComputableSplit`'s side at all). -/
noncomputable def splitFromBisection (A : Set α) (B' : Set γ) (Xn : Set α) : Set γ × Set γ :=
  if h : ∃ n m k, A = P.X n ∧ B' = Q.X m ∧ Xn = P.X k then
    if emptyInterDec P (Nat.pair h.choose h.choose_spec.choose_spec.choose) = 1 then
      (∅, B')
    else if emptyDiffDec P hDiff (Nat.pair h.choose h.choose_spec.choose_spec.choose) = 1 then
      (B', ∅)
    else
      (Q.X (B.left h.choose_spec.choose), Q.X (B.right h.choose_spec.choose))
  else
    splitChoice' W hWnomin A B' Xn

end ComputableBisection

end DomainTheory.NeighbourhoodSystems
