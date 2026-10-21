/-ai
The cross-combine of two coded lists, and the flat-map of a list-valued operation on codes, are developed through step equations and membership characterizations.

The cons step on a paired element, accumulator, and parameter equals one more than the pair of the element and the accumulator.

Unfolding the cons step and cancelling the pairing gives the equation.

A natural belongs to the list decoded from the left fold that conses the elements of a list onto an accumulator if and only if it belongs to that list or to the list decoded from the accumulator.

The proof is by induction on the list. The empty list is immediate. At a cons cell, the fold equation and the cons-step equation replace the accumulator by one more than the pair of the head and the previous accumulator. The inductive hypothesis and the successor rule for decoding split membership into the tail, the head, or the previous accumulator, and the two directions rearrange those three cases.

A natural belongs to the list decoded from the append of two codes if and only if it belongs to the list decoded from the first code or the list decoded from the second.

Unfolding append and rewriting the fold by its list equation, the auxiliary membership lemma applies to the list decoded from the first code with the second code as accumulator.

The inner step of a binary operation, on a paired element, accumulator, and fixed argument, equals one more than the pair of the operation on that argument and the element with the accumulator.

Unfolding the inner step and cancelling the pairing gives the equation.

A natural belongs to the list decoded from the left fold of the inner step at a fixed first argument if and only if it equals the operation on that argument and some element of the list, or it belongs to the list decoded from the accumulator.

The proof is by induction on the list. The empty list is immediate. At a cons cell, the fold equation and the inner-step equation replace the accumulator, the inductive hypothesis applies, and the successor rule for decoding splits membership. The two directions rearrange the witness in the tail, the head, and the previous accumulator.

A natural belongs to the list decoded from the inner cross of a binary operation at a first argument and a list code if and only if it equals the operation on that argument and some element of the decoded list.

Unfolding the inner cross and rewriting the fold by its list equation, the auxiliary membership lemma at the empty accumulator applies, and the empty decoded list contributes no element.

The outer step of a binary operation, on a paired element, accumulator, and list code, equals the append of the inner cross at that element and code with the accumulator.

Unfolding the outer step and cancelling the pairing gives the equation.

A natural belongs to the list decoded from the left fold of the outer step if and only if it equals the operation on some element of the list and some element of the decoded second code, or it belongs to the list decoded from the accumulator.

The proof is by induction on the list. The empty list is immediate. At a cons cell, the fold equation and the outer-step equation replace the accumulator by an append of an inner cross. The inductive hypothesis, membership for append, and membership for the inner cross split the cases, and the two directions rearrange the witness in the tail, at the head, and in the previous accumulator.

The flat-map step of a list-valued operation, on a paired element, accumulator, and fixed argument, equals the append of the list coded by the operation on that argument and the element with the accumulator.

Unfolding the flat-map step and cancelling the pairing gives the equation.

A natural belongs to the list decoded from the left fold of the flat-map step at a fixed first argument if and only if it belongs to the list decoded from the operation on that argument and some element of the list, or it belongs to the list decoded from the accumulator.

The proof is by induction on the list. The empty list is immediate. At a cons cell, the fold equation and the flat-map-step equation replace the accumulator by an append. The inductive hypothesis and membership for append split the cases, and the two directions rearrange the witness in the tail, in the image of the head, and in the previous accumulator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.consStep2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.appendCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.crossInnerStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.crossInner
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.crossOuterStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.crossCombine
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.flatMapStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.flatMapCode

@[expose] public section

/-!
# A choice-free primitive-recursive "cross-combine" of two coded lists

`Definition87.lean`'s `combineIntervals L1 L2 := L1.flatMap (fun p => L2.map (fun q => bop p q))`
needs a code-level analogue: given two `List ℕ` codes `c1, c2` (`Recursive.lean`'s `encodeList`
convention) and a primitive-recursive binary operation `bop`, produce the code of the list of all
`bop x y` for `x` ranging over `c1`'s list and `y` over `c2`'s list.

This extends `Recursive.lean`'s existing two-combinator toolkit (`mapPairCode`, itself built from
`foldCode`) with a genuine **nested** fold: an outer fold over `c1` whose accumulator at each step
is extended by an *inner* fold over `c2` (via `appendCode`, list concatenation on codes). Since the
downstream use (`combineIntervals`, realizing set unions) never cares about list order or
duplicates, correctness is stated at the level of list **membership**, not exact list equality —
this sidesteps tracking the reversals `foldCode`'s left-to-right consing introduces.

Everything here is `⊆ {propext, Quot.sound}`.
-/

namespace Domain.Recursive

/-! ### `appendCode`: concatenation of two coded lists (up to order) -/



theorem consStep2_eq (x acc params : ℕ) :
    consStep2 (Nat.pair x (Nat.pair acc params)) = Nat.pair x acc + 1 := by
  unfold consStep2; simp only [unpair_pair_fst, unpair_pair_snd]

theorem mem_decodeList_appendCode_aux :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList (List.foldl (fun acc x => consStep2 (Nat.pair x (Nat.pair acc 0))) acc l)
        ↔ z ∈ l ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, consStep2_eq, mem_decodeList_appendCode_aux l (Nat.pair a acc + 1) z,
      decodeList_succ, unpair_pair_fst, unpair_pair_snd]
    simp only [List.mem_cons]
    constructor
    · rintro (hl | (rfl | hacc))
      · exact Or.inl (Or.inr hl)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hacc
    · rintro ((rfl | hl) | hacc)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hl
      · exact Or.inr (Or.inr hacc)

theorem mem_decodeList_appendCode (c1 c2 z : ℕ) :
    z ∈ decodeList (appendCode c1 c2) ↔ z ∈ decodeList c1 ∨ z ∈ decodeList c2 := by
  unfold appendCode
  rw [foldCode_eq', mem_decodeList_appendCode_aux (decodeList c1) c2 z]

/-! ### `crossInner`: `bop x` mapped over a coded list -/



theorem crossInnerStep_eq (bop : ℕ → ℕ) (y acc x : ℕ) :
    crossInnerStep bop (Nat.pair y (Nat.pair acc x)) = Nat.pair (bop (Nat.pair x y)) acc + 1 := by
  unfold crossInnerStep; simp only [unpair_pair_fst, unpair_pair_snd]

private theorem mem_decodeList_crossInner_aux (bop : ℕ → ℕ) (x : ℕ) :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList
          (List.foldl (fun acc y => crossInnerStep bop (Nat.pair y (Nat.pair acc x))) acc l)
        ↔ (∃ y ∈ l, z = bop (Nat.pair x y)) ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, crossInnerStep_eq,
      mem_decodeList_crossInner_aux bop x l (Nat.pair (bop (Nat.pair x a)) acc + 1) z,
      decodeList_succ, unpair_pair_fst, unpair_pair_snd]
    simp only [List.mem_cons]
    constructor
    · rintro (⟨y, hy, heq⟩ | (rfl | hacc))
      · exact Or.inl ⟨y, Or.inr hy, heq⟩
      · exact Or.inl ⟨a, Or.inl rfl, rfl⟩
      · exact Or.inr hacc
    · rintro (⟨y, (rfl | hy), heq⟩ | hacc)
      · exact Or.inr (Or.inl heq)
      · exact Or.inl ⟨y, hy, heq⟩
      · exact Or.inr (Or.inr hacc)

theorem mem_decodeList_crossInner {bop : ℕ → ℕ} (x c2 z : ℕ) :
    z ∈ decodeList (crossInner bop x c2) ↔ ∃ y ∈ decodeList c2, z = bop (Nat.pair x y) := by
  unfold crossInner
  rw [foldCode_eq', mem_decodeList_crossInner_aux bop x (decodeList c2) 0 z]
  simp only [decodeList_zero, List.not_mem_nil, or_false]

/-! ### `crossCombine`: the full nested fold -/



theorem crossOuterStep_eq (bop : ℕ → ℕ) (x acc c2 : ℕ) :
    crossOuterStep bop (Nat.pair x (Nat.pair acc c2)) = appendCode (crossInner bop x c2) acc := by
  unfold crossOuterStep; simp only [unpair_pair_fst, unpair_pair_snd]

theorem mem_decodeList_crossCombine_aux (bop : ℕ → ℕ) (c2 : ℕ) :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList (List.foldl (fun acc x => crossOuterStep bop (Nat.pair x (Nat.pair acc c2)))
          acc l)
        ↔ (∃ x ∈ l, ∃ y ∈ decodeList c2, z = bop (Nat.pair x y)) ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, crossOuterStep_eq,
      mem_decodeList_crossCombine_aux bop c2 l (appendCode (crossInner bop a c2) acc) z,
      mem_decodeList_appendCode, mem_decodeList_crossInner]
    simp only [List.mem_cons]
    constructor
    · rintro (⟨x, hx, y, hy, heq⟩ | (⟨y, hy, heq⟩ | hacc))
      · exact Or.inl ⟨x, Or.inr hx, y, hy, heq⟩
      · exact Or.inl ⟨a, Or.inl rfl, y, hy, heq⟩
      · exact Or.inr hacc
    · rintro (⟨x, (rfl | hx), y, hy, heq⟩ | hacc)
      · exact Or.inr (Or.inl ⟨y, hy, heq⟩)
      · exact Or.inl ⟨x, hx, y, hy, heq⟩
      · exact Or.inr (Or.inr hacc)

/-! ### `flatMapCode`: `f x` (list-valued) flat-mapped over a coded list

Like `crossInner`, but the per-element operation `f` returns the *code of a list* to be
**appended** (`appendCode`) onto the accumulator, rather than a single value to be *consed* — the
code-level analogue of `l.flatMap (fun y => decodeList (f x y))`. This is the piece
`Theorem88b`'s interval-*difference* needs: subtracting a whole interval-list from a single
interval can produce `0`, `1`, or `2` result-pieces per step, so the per-element result is itself
list-valued. -/



theorem flatMapStep_eq (f : ℕ → ℕ) (y acc x : ℕ) :
    flatMapStep f (Nat.pair y (Nat.pair acc x)) = appendCode (f (Nat.pair x y)) acc := by
  unfold flatMapStep; simp only [unpair_pair_fst, unpair_pair_snd]

theorem mem_decodeList_flatMapCode_aux (f : ℕ → ℕ) (x : ℕ) :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList (List.foldl (fun acc y => flatMapStep f (Nat.pair y (Nat.pair acc x))) acc l)
        ↔ (∃ y ∈ l, z ∈ decodeList (f (Nat.pair x y))) ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, flatMapStep_eq,
      mem_decodeList_flatMapCode_aux f x l (appendCode (f (Nat.pair x a)) acc) z,
      mem_decodeList_appendCode]
    simp only [List.mem_cons]
    constructor
    · rintro (⟨y, hy, hz⟩ | (hfa | hacc))
      · exact Or.inl ⟨y, Or.inr hy, hz⟩
      · exact Or.inl ⟨a, Or.inl rfl, hfa⟩
      · exact Or.inr hacc
    · rintro (⟨y, (rfl | hy), hz⟩ | hacc)
      · exact Or.inr (Or.inl hz)
      · exact Or.inl ⟨y, hy, hz⟩
      · exact Or.inr (Or.inr hacc)
end Domain.Recursive
