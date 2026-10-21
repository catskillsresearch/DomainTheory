/-ai
Two lists of rational pairs that have the same members present the same set of reals.

Extensionality reduces the claim to a witnessing pair. A pair in one list is a pair in the other by the membership equivalence, with the same endpoint bounds.

The difference of the half-open intervals from a to b and from c to d is the union of the interval from a to the meet of b and c and the interval from the join of a and d to b.

Extensionality and the membership rules for difference, intervals, unions, meets, and joins give both directions. If a point lies in the first interval and misses the second, then either it lies below c, giving the left piece, or it is at least c and hence at least d, giving the right piece, since it cannot lie strictly below d. Each piece lies in the first interval, and its endpoint comparison contradicts one bound of the second interval.

The two-element list of those pieces presents the difference of the two intervals.

Unfold the list and rewrite by the cons and nil presentation laws, then apply the interval-difference identity.

Subtracting one rational pair from a presenting list presents the difference of the presented set with that pair's interval.

The empty list simplifies. For a cons cell, the concatenation of the one-pair difference with the difference of the tail, the append and one-pair presentation laws, the inductive hypothesis, and the cons presentation law match the distribution of set difference over union.

Decoding the one-pair difference code of a paired code returns the one-pair difference of the two decoded rational pairs.

Unfold the code, the list decoding, the two-element list, and the pair decoding. Simplify unpairing and the decoding of a successor list and of the empty list, then rewrite the rational minimum and maximum codes.

A rational pair lies in the decoding of a flat-mapped code if and only if it lies in the decoding of the function applied to the pair of the parameter with some entry of the decoded list.

Unfold the decoding and use membership in a mapped list. An entry of the flat-mapped list comes from the function at some decoded-list entry, and the pair is then in the decoding of that value. Conversely, a pair in such a decoding is the decoding of an entry of the function value, and that entry lies in the flat-mapped list.

A rational pair lies in the decoding of the single-difference code if and only if it lies in the single-difference list of the decoded accumulator and the decoded pair.

Unfold the code and rewrite by the flat-map membership theorem and the decoding of the one-pair code. Unfolding the list and the decoding, a decoded accumulator entry corresponds to an entry of the decoded list, and conversely.

The decoded single-difference code presents the difference of the decoded accumulator with the interval of the decoded pair.

The membership congruence and the list-level presentation of a single difference give the equality.

The fold step at the pair of a code x with the pair of an accumulator and zero is the single-difference code of that accumulator and x.

Unfold the step and simplify unpairing.

Folding the difference step over a list of codes presents the difference of the decoded accumulator with the presentation of the decoded pairs.

The empty fold leaves the accumulator. For a cons cell, the fold equation, the identification of the step, the inductive hypothesis, the single-difference presentation, and the cons presentation law match successive set differences.

The whole-list difference code presents the difference of the decoded single interval with the decoded list.

Unfold the code, apply the fold-code equation and the fold presentation, and simplify the seed decoding to one interval by the successor, empty, cons, and nil presentation laws.

A rational pair lies in the decoding of the two-list difference code if and only if it lies in the decoding of the whole-list difference of some entry of the first code.

Unfold the code, rewrite by flat-map membership, and simplify unpairing in the witness.

The flat map of whole-list difference decodings presents the difference of the decoded pairs with the second decoded list.

The empty flat map simplifies. For a cons cell, the append presentation, the whole-list presentation, the inductive hypothesis, and the cons presentation law match the distribution of set difference over union.

The two-list difference code presents the difference of the two decoded presentations.

The membership congruence, rewritten through the membership theorem and flat-map membership, together with the flat-map presentation, leaves the decoding of the first list equal to itself.

A presented union of rational intervals is nonempty if and only if some pair in the list has left endpoint strictly below the right endpoint.

A point of the union lies in some pair's interval, so that pair is nondegenerate. Conversely, the left endpoint of a nondegenerate pair lies in its interval and hence in the union.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.encodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.qpCombineBop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.combineCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffOneList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffSingleList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffAllList
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffLists
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffOneCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffSingleCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffAllStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffAllCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.diffCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.qpNonemptyBop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.qpNonemptyChar
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_encodeRatPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeQPairList_encodeQPairList

@[expose] public section

/-!
# Primitive-recursive interval-list arithmetic for `𝒰` (Definition 8.7)

Builds the code-level analogue of `Definition87.lean`'s `List (ℚ × ℚ)` interval-presentation
machinery: encoding `List (ℚ × ℚ)` by `ℕ` (reusing `RationalPrimrec.lean`'s rational codes and
`Recursive.lean`'s `encodeList`), a genuinely `Nat.Primrec` **`combineCode`** realizing
`combineIntervals` at the code level (via `RecursiveCross.lean`'s `crossCombine`), and a
**canonicalization** `canonCode` that clips every code to a bona fide `𝒰`-neighbourhood (nonempty,
`⊆ [0,1)`), needed so `𝒰`'s eventual `ComputablePresentation.X` (`Definition71.lean`) is *total*
(every code indexes an actual neighbourhood).

All the `Nat.Primrec`/encoding results here are `⊆ {propext, Quot.sound}`. The set-level correctness
lemmas (`presentedIntervals_decodeQPairList_combineCode` and its helpers) additionally report
`Classical.choice` in `#print axioms`, but — exactly as documented in `Definition87.lean`'s own
"Axiom footprint" section — this is inherited from the *pinned Mathlib's* `ℚ` order instance itself
being `Classical.choice`-tainted, not from any classical reasoning performed in this file.
-/

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-! ### Encoding `List (ℚ × ℚ)` -/







/-! ### `combineIntervals` at the code level -/



/-- Two lists with the same **elements** present the same set. -/
theorem presentedIntervals_congr {L1 L2 : List (ℚ × ℚ)} (h : ∀ p, p ∈ L1 ↔ p ∈ L2) :
    presentedIntervals L1 = presentedIntervals L2 := by
  ext x
  simp only [mem_presentedIntervals]
  constructor
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, (h p).mp hp, h1, h2⟩
  · rintro ⟨p, hp, h1, h2⟩; exact ⟨p, (h p).mpr hp, h1, h2⟩

/-! ## Interval-list *difference*, needed for subset/equality decidability

`ComputablePresentation`'s relations (i)/(ii) (`Definition71.lean`) both ultimately reduce to
deciding whether one presented set is *empty* or a *subset* of another. Non-emptiness is a cheap
bounded-`∃` (`p.1 < p.2` for some `p` in the list, via `Recursive.lean`'s `existsListChar`), but
subset needs genuine interval-covering arithmetic: `L1 ⊆ L2 ↔ presentedIntervals L1 \ presentedIntervals L2
= ∅`, computed here by an explicit `diffLists`. As with `combineIntervals`, everything is built from
the *unconditional* identity `Set.Ico_diff_Ico` (no side conditions on endpoint order), first at the
pure list level (`diffOneList`/`diffSingleList`/`diffAllList`/`diffLists`), then mirrored at the
`Nat.Primrec` code level (`diffOneCode`/`diffSingleCode`/`diffAllCode`/`diffCode`) via
`RecursiveCross.lean`'s `flatMapCode`. -/

/-- **Unconditional interval difference**: `Ico a b \ Ico c d = Ico a (b ⊓ c) ∪ Ico (a ⊔ d) b`, with
no ordering hypotheses on `a, b, c, d` (mirrors `Set.Ico_inter_Ico`'s unconditional intersection
formula). -/
theorem Ico_diff_Ico (a b c d : ℚ) :
    Set.Ico a b \ Set.Ico c d = Set.Ico a (b ⊓ c) ∪ Set.Ico (a ⊔ d) b := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_union, lt_inf_iff, sup_le_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, hcd⟩
    rcases lt_or_ge x c with hc | hc
    · exact Or.inl ⟨ha, hb, hc⟩
    · rcases lt_or_ge x d with hd | hd
      · exact absurd ⟨hc, hd⟩ hcd
      · exact Or.inr ⟨⟨ha, hd⟩, hb⟩
  · rintro (⟨ha, hb, hc⟩ | ⟨⟨ha, hd⟩, hb⟩)
    · exact ⟨⟨ha, hb⟩, fun ⟨hc', _⟩ => absurd hc' (not_le.mpr hc)⟩
    · exact ⟨⟨ha, hb⟩, fun ⟨_, hd'⟩ => absurd hd' (not_lt.mpr hd)⟩


theorem presentedIntervals_diffOneList (p q : ℚ × ℚ) :
    presentedIntervals (diffOneList p q) = Set.Ico p.1 p.2 \ Set.Ico q.1 q.2 := by
  unfold diffOneList
  rw [presentedIntervals_cons, presentedIntervals_cons, presentedIntervals_nil, Set.union_empty]
  exact (Ico_diff_Ico p.1 p.2 q.1 q.2).symm


theorem presentedIntervals_diffSingleList (L : List (ℚ × ℚ)) (q : ℚ × ℚ) :
    presentedIntervals (diffSingleList L q) = presentedIntervals L \ Set.Ico q.1 q.2 := by
  induction L with
  | nil => simp [diffSingleList]
  | cons a l ih =>
    rw [show diffSingleList (a :: l) q = diffOneList a q ++ diffSingleList l q from rfl,
      presentedIntervals_append, presentedIntervals_diffOneList, ih, presentedIntervals_cons,
      Set.union_sdiff_distrib]



/-! ### The code level: `diffOneCode`/`diffSingleCode`/`diffAllCode`/`diffCode` -/


theorem decodeQPairList_diffOneCode (qc pc : ℕ) :
    decodeQPairList (diffOneCode (Nat.pair qc pc)) = diffOneList (decodeRatPair pc) (decodeRatPair qc) := by
  unfold diffOneCode decodeQPairList diffOneList decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd, decodeList_succ, decodeList_zero, List.map_cons,
    List.map_nil]
  rw [decodeRat_ratMinCode, decodeRat_ratMaxCode]

/-- **`flatMapCode`'s membership correctness, lifted to `decodeQPairList`.** -/
theorem mem_decodeQPairList_flatMapCode (f : ℕ → ℕ) (x c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (flatMapCode f x c) ↔ ∃ y ∈ decodeList c, p ∈ decodeQPairList (f (Nat.pair x y)) := by
  unfold decodeQPairList
  rw [List.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_decodeList_flatMapCode] at hz
    obtain ⟨y, hy, hz'⟩ := hz
    exact ⟨y, hy, List.mem_map_of_mem hz'⟩
  · rintro ⟨y, hy, hp⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    exact ⟨e, (mem_decodeList_flatMapCode (f := f) x c e).mpr ⟨y, hy, he⟩, rfl⟩


theorem mem_decodeQPairList_diffSingleCode (accL q : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (diffSingleCode accL q) ↔ p ∈ diffSingleList (decodeQPairList accL) (decodeRatPair q) := by
  unfold diffSingleCode
  rw [mem_decodeQPairList_flatMapCode]
  simp only [decodeQPairList_diffOneCode]
  unfold diffSingleList decodeQPairList
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨y, hy, hp⟩; exact ⟨decodeRatPair y, ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p', ⟨y, hy, rfl⟩, hp⟩; exact ⟨y, hy, hp⟩

theorem presentedIntervals_decodeQPairList_diffSingleCode (accL q : ℕ) :
    presentedIntervals (decodeQPairList (diffSingleCode accL q))
      = presentedIntervals (decodeQPairList accL) \ Set.Ico (decodeRatPair q).1 (decodeRatPair q).2 := by
  rw [presentedIntervals_congr (mem_decodeQPairList_diffSingleCode accL q), presentedIntervals_diffSingleList]



theorem diffAllStep_eq (acc x : ℕ) : diffAllStep (Nat.pair x (Nat.pair acc 0)) = diffSingleCode acc x := by
  unfold diffAllStep; simp only [unpair_pair_fst, unpair_pair_snd]

theorem presentedIntervals_decodeQPairList_foldl_diffAllStep (L2list : List ℕ) :
    ∀ acc : ℕ, presentedIntervals (decodeQPairList
        (List.foldl (fun acc x => diffAllStep (Nat.pair x (Nat.pair acc 0))) acc L2list))
      = presentedIntervals (decodeQPairList acc) \ presentedIntervals (L2list.map decodeRatPair) := by
  induction L2list with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons, diffAllStep_eq, ih (diffSingleCode acc a),
      presentedIntervals_decodeQPairList_diffSingleCode, List.map_cons, presentedIntervals_cons,
      Set.sdiff_sdiff]

theorem presentedIntervals_decodeQPairList_diffAllCode (pc L2 : ℕ) :
    presentedIntervals (decodeQPairList (diffAllCode pc L2))
      = Set.Ico (decodeRatPair pc).1 (decodeRatPair pc).2 \ presentedIntervals (decodeQPairList L2) := by
  unfold diffAllCode
  rw [foldCode_eq', presentedIntervals_decodeQPairList_foldl_diffAllStep]
  unfold decodeQPairList
  simp only [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero, List.map_cons,
    List.map_nil, presentedIntervals_cons, presentedIntervals_nil, Set.union_empty]


theorem mem_decodeQPairList_diffCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (diffCode c1 c2) ↔ ∃ y ∈ decodeList c1, p ∈ decodeQPairList (diffAllCode y c2) := by
  unfold diffCode
  rw [mem_decodeQPairList_flatMapCode]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem presentedIntervals_decodeQPairList_flatMap_diffAllCode (c1list : List ℕ) (c2 : ℕ) :
    presentedIntervals (c1list.flatMap (fun y => decodeQPairList (diffAllCode y c2)))
      = presentedIntervals (c1list.map decodeRatPair) \ presentedIntervals (decodeQPairList c2) := by
  induction c1list with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_cons, presentedIntervals_append,
      presentedIntervals_decodeQPairList_diffAllCode, ih, presentedIntervals_cons,
      Set.union_sdiff_distrib]

/-- **`diffCode` realizes `diffLists` (hence set difference) at the set level.** -/
theorem presentedIntervals_decodeQPairList_diffCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (diffCode c1 c2))
      = presentedIntervals (decodeQPairList c1) \ presentedIntervals (decodeQPairList c2) := by
  rw [presentedIntervals_congr
      (fun p => (mem_decodeQPairList_diffCode c1 c2 p).trans (List.mem_flatMap).symm),
    presentedIntervals_decodeQPairList_flatMap_diffAllCode]
  rfl

/-! ## Decidability of non-emptiness, subset, and equality of `presentedIntervals`

`ComputablePresentation`'s relations (i)/(ii) (`Definition71.lean`) reduce, via `𝒰`'s canonical
enumeration (Part 3), to deciding membership questions about `presentedIntervals`-coded sets. The
key primitive is **non-emptiness**: `presentedIntervals L` is non-empty iff some pair `p ∈ L` has
`p.1 < p.2` (`presentedIntervals_nonempty_iff`), a cheap bounded-`∃` over the list
(`Recursive.lean`'s `existsListChar`). Subset and equality then reduce to non-emptiness of
`diffCode`, reusing `presentedIntervals_decodeQPairList_diffCode` above — no new arithmetic is
needed. -/

/-- **A presented union of intervals is non-empty iff some pair in the list is itself non-degenerate**
(`p.1 < p.2`): every degenerate pair contributes the empty interval, and a single non-degenerate pair
already witnesses non-emptiness (via its left endpoint). -/
theorem presentedIntervals_nonempty_iff (L : List (ℚ × ℚ)) :
    (presentedIntervals L).Nonempty ↔ ∃ p ∈ L, p.1 < p.2 := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨p, hp, hx1, hx2⟩ := mem_presentedIntervals.mp hx
    exact ⟨p, hp, lt_of_le_of_lt hx1 hx2⟩
  · rintro ⟨p, hp, hlt⟩
    exact ⟨p.1, mem_presentedIntervals.mpr ⟨p, hp, le_refl _, hlt⟩⟩


end DomainTheory.NeighbourhoodSystems
