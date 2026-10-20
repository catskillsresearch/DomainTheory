/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.ComputableBisection

@[expose] public section

/-!
# Exercise 8.12(e) (Scott 1981, PRG-19, Lecture VIII) — `U` satisfies the extension property
relative to `V`

## 8.12(e)(a): the split's contract, as Lean declarations

`(d)`'s `IsComputableSplit P Q split` structure only ever gets *consumed*, downstream, through its
two index functions `posIdx`/`negIdx : ℕ → ℕ → ℕ → ℕ` (`xSubStep`/`ySubStep`, `Exercise812d.lean`).
This section fixes the *design* for those two functions concretely, as genuine `Nat`-valued `def`s
(no proof obligations yet — those are `(e)(c)`'s job): given a prober presentation `P` (with an
`IsComputableDiff` witness) and a target presentation `Q` equipped with a computable canonical
bisection (`ComputableBisection`, below), decide via the prober's own `emptyInterDec`/`emptyDiffDec`
deciders ((d)(2)) whether the "chosen branch" is (as far as these two deciders can tell) forced
empty, and fall back to the bisection only when neither decider fires.

Both `posIdxFromBisection`/`negIdxFromBisection` share the same outer shape and, not entirely
obviously, the same "either decider fires" branch value `m` (i.e. literally `B` itself) — one of the
two decider branches is the *genuinely correct* value in that case (`A ⊆ Xn` resp. `Xn ∩ A = ∅`
forces the corresponding piece to be exactly `B`), the other is a harmless placeholder that later
gets junk-masked (`xSubStep`'s `newJunk`) before ever being read — see the `(e)(a)` row of
`arxiv.md` for the case-by-case argument. Only the "both deciders silent" branch genuinely bisects
`B`, via the supplied `ComputableBisection`. -/

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

/-- **The split's "negative" (`\`-branch) index.** Same outer shape as `posIdxFromBisection`,
falling back to the bisection's *right* half instead of its left. -/
noncomputable def negIdxFromBisection (n m k : ℕ) : ℕ :=
  selectFn (emptyInterDec P (Nat.pair n k)) m
    (selectFn (emptyDiffDec P hDiff (Nat.pair n k)) m (B.right m))

/-! ### 8.12(e)(c)(i): decider congruence and index-function well-definedness

`emptyInterDec`/`emptyDiffDec` depend only on the *sets* `P.X n ∩ P.X k`/`P.X n \ P.X k` (via
`(d)(2)`'s `_eq_one_iff` characterizations), not on which raw index presents them — and, combined
with `left_congr`/`right_congr` above, this transports all the way up to `posIdxFromBisection`/
`negIdxFromBisection` being well-defined functions of sets, exactly what `(e)(c)(ii)`'s
`posIdx_spec`/`negIdx_spec` will need. -/

section Congr

variable {n n' k k' m m' : ℕ}

/-- `emptyInterDec` is a well-defined function of the two *sets* `P.X n`, `P.X k`: it does not
distinguish between different raw indices presenting the same set. -/
theorem emptyInterDec_congr (hpos : V.IsPositive) (hnomin : V.NoMinimal)
    (hn : P.X n = P.X n') (hk : P.X k = P.X k') :
    emptyInterDec P (Nat.pair n k) = emptyInterDec P (Nat.pair n' k') := by
  have h1 := emptyInterDec_eq_one_iff P hpos hnomin n k
  have h2 := emptyInterDec_eq_one_iff P hpos hnomin n' k'
  rw [hn, hk] at h1
  have hiff : emptyInterDec P (Nat.pair n k) = 1 ↔ emptyInterDec P (Nat.pair n' k') = 1 :=
    h1.trans h2.symm
  have hle1 := emptyInterDec_le_one P (Nat.pair n k)
  have hle2 := emptyInterDec_le_one P (Nat.pair n' k')
  omega

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

/-! ### 8.12(e)(c)(ii): `splitFromBisection` and `isComputableSplit_ofBisection`

The actual classical split, and its `IsComputableSplit` proof, completing `8.12(e)(c)`. Genuinely
new work beyond `(e)(c)(i)`: the two index functions' *joint* primitive-recursiveness (as a single
function of the packed triple `Nat.pair n (Nat.pair m k)`, `IsComputableSplit`'s own convention) was
not yet proved — `posIdxFromBisection`/`negIdxFromBisection` are primitive recursive in each
*argument* separately (from their own defining pieces) but had not yet been packaged as one
triple-argument `Nat.Primrec` witness. **Deviation from the `arxiv.md` draft signature**:
`splitFromBisection` itself takes only `P`, `hDiff`, `B` (not `hpos`/`hnomin`/`hdiffClosed`) — those
three hypotheses are needed only for *correctness* (`isComputableSplit_ofBisection`'s `posIdx_spec`/
`negIdx_spec`, via `(e)(c)(i)`'s congruence lemmas), never for the definition itself, mirroring how
`posIdxFromBisection`/`negIdxFromBisection` are themselves already hypothesis-free to *define*. -/

theorem primrec_posIdxFromBisection :
    Nat.Primrec (fun t => posIdxFromBisection P hDiff B
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hnk : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2.unpair.2) := hn.pair hk
  have hinter : Nat.Primrec
      (fun t : ℕ => emptyInterDec P (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (primrec_emptyInterDec P).comp hnk
  have hdiffD : Nat.Primrec
      (fun t : ℕ => emptyDiffDec P hDiff (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (primrec_emptyDiffDec P hDiff).comp hnk
  have hleft : Nat.Primrec (fun t : ℕ => B.left t.unpair.2.unpair.1) := B.left_primrec.comp hm
  have hinner : Nat.Primrec (fun t : ℕ => selectFn
      (emptyDiffDec P hDiff (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) t.unpair.2.unpair.1
      (B.left t.unpair.2.unpair.1)) :=
    primrec_selectFn hdiffD hm hleft
  exact (primrec_selectFn hinter hm hinner).of_eq fun _ => rfl

theorem primrec_negIdxFromBisection :
    Nat.Primrec (fun t => negIdxFromBisection P hDiff B
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hnk : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2.unpair.2) := hn.pair hk
  have hinter : Nat.Primrec
      (fun t : ℕ => emptyInterDec P (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (primrec_emptyInterDec P).comp hnk
  have hdiffD : Nat.Primrec
      (fun t : ℕ => emptyDiffDec P hDiff (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (primrec_emptyDiffDec P hDiff).comp hnk
  have hright : Nat.Primrec (fun t : ℕ => B.right t.unpair.2.unpair.1) := B.right_primrec.comp hm
  have hinner : Nat.Primrec (fun t : ℕ => selectFn
      (emptyDiffDec P hDiff (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) t.unpair.2.unpair.1
      (B.right t.unpair.2.unpair.1)) :=
    primrec_selectFn hdiffD hm hright
  exact (primrec_selectFn hinter hm hinner).of_eq fun _ => rfl

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
