module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_8
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **A computable canonical bisection of a `ComputablePresentation`'s own neighbourhoods**: two
`Nat.Primrec` index functions `left`/`right` such that `Q.X (left k)`/`Q.X (right k)` are always
disjoint and reunite to `Q.X k`. (Nonemptiness of both pieces is *not* required here — for the
concrete `U`/`V` instances this file eventually builds (`(e)(b)`/`SplitU.lean`), it is automatic
from `mem → Set.Nonempty`, so is proved separately rather than carried as a field.)

**`left_congr`/`right_congr`** are a well-definedness requirement discovered while scoping `(e)(c)`
(2026-07-05), *not* present in the earlier `arxiv.md` draft of this structure: `ComputablePresentation.X`
is generally many-to-one (distinct raw indices `k`, `k'` can present the *same* set `Q.X k = Q.X k'`),
so building a genuine classical `split : Set α → Set γ → Set α → Set γ × Set γ` *function of sets*
out of an index-level `left`/`right` needs `left`/`right`'s *output sets* — not necessarily the raw
output indices themselves — to only depend on `Q.X k` as a set, or `(e)(c)`'s `posIdx_spec`/
`negIdx_spec` obligations (stated `∀ n m k`, not just for one fixed representative) would not be
provable. Satisfied by any canonicalizing construction (e.g. `SplitU.lean`'s `splitULeft`/
`splitURight`, built via `canonCode`, which already collapses every representative of a given set to
one canonical index) — expected free for both `(e)(b)`'s `SplitV.lean` and `(f)(a)`'s reuse of
`SplitU.lean`, but must be checked (or reduced to an existing `canonCode`/`canonIdx`-invariance lemma)
when those are actually built, not merely assumed. -/
structure ComputableBisection {γ : Type*} {W : NeighborhoodSystem γ} (Q : ComputablePresentation W) where
  /-- Index of the "left" half of `Q.X k`. -/
  left : ℕ → ℕ
  /-- Index of the "right" half of `Q.X k`. -/
  right : ℕ → ℕ
  /-- `left` is primitive recursive. -/
  left_primrec : Nat.Primrec left
  /-- `right` is primitive recursive. -/
  right_primrec : Nat.Primrec right
  /-- The two halves are disjoint. -/
  disjoint : ∀ k, Q.X (left k) ∩ Q.X (right k) = ∅
  /-- The two halves reunite to the whole. -/
  union : ∀ k, Q.X (left k) ∪ Q.X (right k) = Q.X k
  /-- `left`'s *output set* depends only on `Q.X k` as a set, not on which raw index represents it. -/
  left_congr : ∀ k k', Q.X k = Q.X k' → Q.X (left k) = Q.X (left k')
  /-- `right`'s *output set* depends only on `Q.X k` as a set, not on which raw index represents it. -/
  right_congr : ∀ k k', Q.X k = Q.X k' → Q.X (right k) = Q.X (right k')

end DomainTheory.NeighbourhoodSystems

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

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

/-- **The split's "negative" (`\`-branch) index.** Same outer shape as `posIdxFromBisection`,
falling back to the bisection's *right* half instead of its left. -/
noncomputable def negIdxFromBisection (n m k : ℕ) : ℕ :=
  selectFn (emptyInterDec P (Nat.pair n k)) m
    (selectFn (emptyDiffDec P hDiff (Nat.pair n k)) m (B.right m))

end ComputableBisection

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

section Congr

variable {n n' k k' m m' : ℕ}

namespace emptyDiffDec
/-- `emptyDiffDec` is a well-defined function of the two *sets* `P.X n`, `P.X k`: it does not
distinguish between different raw indices presenting the same set. Needs `V.DiffClosed`, not just
`IsComputableDiff P` — a hypothesis gap found while scoping `(e)(c)` (2026-07-05), absent from
`(e)(c)`'s original draft signature. -/
theorem congr (hdiffClosed : V.DiffClosed) (hnomin : V.NoMinimal)
    (hn : P.X n = P.X n') (hk : P.X k = P.X k') :
    emptyDiffDec P hDiff (Nat.pair n k) = emptyDiffDec P hDiff (Nat.pair n' k') := by
  have h1 := emptyDiffDec.eq_one_iff P hDiff hdiffClosed hnomin n k
  have h2 := emptyDiffDec.eq_one_iff P hDiff hdiffClosed hnomin n' k'
  rw [hn, hk] at h1
  have hiff : emptyDiffDec P hDiff (Nat.pair n k) = 1 ↔ emptyDiffDec P hDiff (Nat.pair n' k') = 1 :=
    h1.trans h2.symm
  have hle1 := emptyDiffDec.le_one P hDiff (Nat.pair n k)
  have hle2 := emptyDiffDec.le_one P hDiff (Nat.pair n' k')
  omega

end emptyDiffDec
end Congr

end ComputableBisection

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

section Congr

variable {n n' k k' m m' : ℕ}

namespace emptyInterDec
/-- `emptyInterDec` is a well-defined function of the two *sets* `P.X n`, `P.X k`: it does not
distinguish between different raw indices presenting the same set. -/
theorem congr (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hn : P.X n = P.X n') (hk : P.X k = P.X k') :
    emptyInterDec P (Nat.pair n k) = emptyInterDec P (Nat.pair n' k') := by
  have h1 := emptyInterDec.eq_one_iff P hpos hnomin n k
  have h2 := emptyInterDec.eq_one_iff P hpos hnomin n' k'
  rw [hn, hk] at h1
  have hiff : emptyInterDec P (Nat.pair n k) = 1 ↔ emptyInterDec P (Nat.pair n' k') = 1 :=
    h1.trans h2.symm
  have hle1 := emptyInterDec.le_one P (Nat.pair n k)
  have hle2 := emptyInterDec.le_one P (Nat.pair n' k')
  omega

end emptyInterDec
end Congr

end ComputableBisection

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

namespace splitFromBisection
/-- **`splitFromBisection`, unfolded at a literal presented triple `(P.X n, Q.X m, P.X k)`**,
bridging `Classical.choose`'s own (possibly different) witness back to the literal `n, m, k` given,
via `(e)(c)(i)`'s `emptyInterDec.congr`/`emptyDiffDec.congr` (for the two decider branches) and
`B.left_congr`/`B.right_congr` (for the bisection branch). The one lemma both `posIdx_spec`/
`negIdx_spec` and `splitFromBisection.isSplitSpec'` are built from. -/
theorem eq (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) (n m k : ℕ) :
    splitFromBisection P hDiff B hWnomin (P.X n) (Q.X m) (P.X k) =
      if emptyInterDec P (Nat.pair n k) = 1 then (∅, Q.X m)
      else if emptyDiffDec P hDiff (Nat.pair n k) = 1 then (Q.X m, ∅)
      else (Q.X (B.left m), Q.X (B.right m)) := by
  have hex : ∃ n' m' k', P.X n = P.X n' ∧ Q.X m = Q.X m' ∧ P.X k = P.X k' :=
    ⟨n, m, k, rfl, rfl, rfl⟩
  obtain ⟨hn', hm', hk'⟩ := hex.choose_spec.choose_spec.choose_spec
  have hInterEq : emptyInterDec P (Nat.pair hex.choose hex.choose_spec.choose_spec.choose) =
      emptyInterDec P (Nat.pair n k) := (emptyInterDec.congr P hpos hnomin hn' hk').symm
  have hDiffEq : emptyDiffDec P hDiff (Nat.pair hex.choose hex.choose_spec.choose_spec.choose) =
      emptyDiffDec P hDiff (Nat.pair n k) :=
    (emptyDiffDec.congr P hDiff hdiffClosed hnomin hn' hk').symm
  unfold splitFromBisection
  rw [dite_eq_left hex, hInterEq, hDiffEq]
  split_ifs with h1 h2
  · rfl
  · rfl
  · have hl := (B.left_congr m hex.choose_spec.choose hm').symm
    have hr := (B.right_congr m hex.choose_spec.choose hm').symm
    rw [hl, hr]

end splitFromBisection
end ComputableBisection

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

/-- **The split's "positive" (`∩`-branch) index**, as a genuine `Nat`-valued function of the three
raw indices `n` (of `A` in `P`), `m` (of `B` in `Q`), `k` (of `Xn` in `P`): fall back to `m` (i.e.
literally `B`) the moment either prober-side decider fires, and to the bisection's left half
otherwise. -/
noncomputable def posIdxFromBisection (n m k : ℕ) : ℕ :=
  selectFn (emptyInterDec P (Nat.pair n k)) m
    (selectFn (emptyDiffDec P hDiff (Nat.pair n k)) m (B.left m))

end ComputableBisection

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)


section Congr

variable {n n' k k' m m' : ℕ}


/-- **`posIdxFromBisection` is a well-defined function of sets**: its *output set*
`Q.X (posIdxFromBisection …)` depends only on `P.X n`, `Q.X m`, `P.X k` as sets, not on the raw
indices `n, m, k` chosen to present them. Four-way case split on the two `{0,1}`-valued deciders:
three of the four cases collapse to the shared fallback value `m`/`m'` (needing only `hm`); only the
"both deciders silent" case needs `B.left_congr`. -/
theorem posIdxFromBisection_congr (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) (hn : P.X n = P.X n') (hk : P.X k = P.X k')
    (hm : Q.X m = Q.X m') :
    Q.X (posIdxFromBisection P hDiff B n m k) = Q.X (posIdxFromBisection P hDiff B n' m' k') := by
  unfold posIdxFromBisection
  rw [emptyInterDec.congr P hpos hnomin hn hk, emptyDiffDec.congr P hDiff hdiffClosed hnomin hn hk]
  have hle1 := emptyInterDec.le_one P (Nat.pair n' k')
  have hle2 := emptyDiffDec.le_one P hDiff (Nat.pair n' k')
  have h1 : emptyInterDec P (Nat.pair n' k') = 0 ∨ emptyInterDec P (Nat.pair n' k') = 1 := by omega
  have h2 : emptyDiffDec P hDiff (Nat.pair n' k') = 0 ∨
      emptyDiffDec P hDiff (Nat.pair n' k') = 1 := by omega
  rcases h1 with h1 | h1
  · simp only [h1, selectFn_zero]
    rcases h2 with h2 | h2
    · simp only [h2, selectFn_zero]; exact B.left_congr m m' hm
    · simp only [h2, selectFn_one]; exact hm
  · simp only [h1, selectFn_one]; exact hm

end Congr
end ComputableBisection
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

namespace primrec
theorem negIdxFromBisection :
    Nat.Primrec (fun t => negIdxFromBisection P hDiff B
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hnk : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2.unpair.2) := hn.pair hk
  have hinter : Nat.Primrec
      (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (primrec.emptyInterDec P).comp hnk
  have hdiffD : Nat.Primrec
      (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P hDiff (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (primrec.emptyDiffDec P hDiff).comp hnk
  have hright : Nat.Primrec (fun t : ℕ => B.right t.unpair.2.unpair.1) := B.right_primrec.comp hm
  have hinner : Nat.Primrec (fun t : ℕ => selectFn
      (_root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P hDiff (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) t.unpair.2.unpair.1
      (B.right t.unpair.2.unpair.1)) :=
    primrec_selectFn hdiffD hm hright
  exact (primrec_selectFn hinter hm hinner).of_eq fun _ => rfl

end primrec
end ComputableBisection

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

namespace primrec
theorem posIdxFromBisection :
    Nat.Primrec (fun t => posIdxFromBisection P hDiff B
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hnk : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2.unpair.2) := hn.pair hk
  have hinter : Nat.Primrec
      (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.emptyInterDec P (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (primrec.emptyInterDec P).comp hnk
  have hdiffD : Nat.Primrec
      (fun t : ℕ => _root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P hDiff (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (primrec.emptyDiffDec P hDiff).comp hnk
  have hleft : Nat.Primrec (fun t : ℕ => B.left t.unpair.2.unpair.1) := B.left_primrec.comp hm
  have hinner : Nat.Primrec (fun t : ℕ => selectFn
      (_root_.DomainTheory.NeighbourhoodSystems.emptyDiffDec P hDiff (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) t.unpair.2.unpair.1
      (B.left t.unpair.2.unpair.1)) :=
    primrec_selectFn hdiffD hm hleft
  exact (primrec_selectFn hinter hm hinner).of_eq fun _ => rfl

end primrec
end ComputableBisection

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

namespace isComputableSplit
/-- **`splitFromBisection` satisfies `IsComputableSplit`**, completing `8.12(e)(c)`. `posIdx`/
`negIdx` are literally `posIdxFromBisection`/`negIdxFromBisection`, unchanged from the original
design; the two (now-conditional, `Exercise812d.lean` `(d)(2)`) `_spec` fields case on
`splitFromBisection.eq`'s three branches — the first is immediately vacuous (`.1 = ∅` there,
contradicting `posIdx_spec`'s `≠ ∅` hypothesis, symmetrically for `negIdx_spec`'s second branch), the
other two unfold `posIdxFromBisection`/`negIdxFromBisection`'s own `selectFn` definition against the
same decider values. -/
noncomputable def ofBisection (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hdiffClosed : V.DiffClosed) :
    IsComputableSplit P Q (splitFromBisection P hDiff B hWnomin) where
  posIdx := posIdxFromBisection P hDiff B
  negIdx := negIdxFromBisection P hDiff B
  posIdx_primrec := primrec.posIdxFromBisection P hDiff B
  negIdx_primrec := primrec.negIdxFromBisection P hDiff B
  posIdx_spec n m k hne := by
    rw [splitFromBisection.eq P hDiff B hWnomin hpos hnomin hdiffClosed n m k] at hne ⊢
    split_ifs at hne ⊢ with h1 h2
    · exact absurd rfl hne
    · have h1' : emptyInterDec P (Nat.pair n k) = 0 := by
        have := emptyInterDec.le_one P (Nat.pair n k); omega
      simp [posIdxFromBisection, h1', h2]
    · have h1' : emptyInterDec P (Nat.pair n k) = 0 := by
        have := emptyInterDec.le_one P (Nat.pair n k); omega
      have h2' : emptyDiffDec P hDiff (Nat.pair n k) = 0 := by
        have := emptyDiffDec.le_one P hDiff (Nat.pair n k); omega
      simp [posIdxFromBisection, h1', h2']
  negIdx_spec n m k hne := by
    rw [splitFromBisection.eq P hDiff B hWnomin hpos hnomin hdiffClosed n m k] at hne ⊢
    split_ifs at hne ⊢ with h1 h2
    · simp [negIdxFromBisection, h1]
    · exact absurd rfl hne
    · have h1' : emptyInterDec P (Nat.pair n k) = 0 := by
        have := emptyInterDec.le_one P (Nat.pair n k); omega
      have h2' : emptyDiffDec P hDiff (Nat.pair n k) = 0 := by
        have := emptyDiffDec.le_one P hDiff (Nat.pair n k); omega
      simp [negIdxFromBisection, h1', h2']

end isComputableSplit
end ComputableBisection

end DomainTheory.NeighbourhoodSystems
