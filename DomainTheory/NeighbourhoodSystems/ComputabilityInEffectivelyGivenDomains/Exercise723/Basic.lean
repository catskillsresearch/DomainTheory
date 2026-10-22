/-ai
If the i-th bit of n is set, then i is strictly smaller than n.

Assume the contrary. Then n is at most i, hence strictly smaller than 2 to the power i. The bit hypothesis rewrites by the lemma that a number below that power has the bit false, and decide rejects the resulting Boolean contradiction.

Iterating integer halving one further time halves the already halved value: halfIter n (k + 1) equals halfIter of n divided by 2, taken k times.

Unfold halfIter and apply the successor law for function iteration.

The map sending a paired natural number to halfIter of its two components is primitive recursive.

Division by 2 of the twice-projected right component is primitive recursive. Primitive recursion from the identity with that step equals, after simplifying the unpairing, the constant-iterator form of repeated division by 2.

The map sending a paired natural number to bitAt of its two components is primitive recursive.

It is remainder modulo 2, composed with the primitive-recursive half-iteration map.

The value bitAt n k is at most 1.

Unfold bitAt and close the inequality with omega.

The value bitAt n k equals 1 if and only if the k-th bit of n is set.

Induct on k, keeping n general. At zero the claim is that n modulo 2 equals 1 if and only if the zeroth bit is set, rewritten by the zeroth-bit lemma and the decision of Boolean truth. At a successor, the successor law for half-iteration and the successor law for test bits reduce the claim to the inductive hypothesis at n divided by 2.

The complement of the neighbourhood nbhd n is the set of positions at which a bit of n is set.

Extend the two sets in the position and simplify the definition of nbhd.

If every entry of a finite list L is witnessed by some neighbourhood of a PN-element x whose index has that entry as a set bit, then one neighbourhood of x witnesses every entry of L at once.

The argument is structural recursion on L. The empty list is witnessed by the index 0, using that nbhd 0 is the master neighbourhood and that x contains the master. For a head k and a tail, take the witness for k and the recursive witness for the tail, and combine their indices by myLor. The combined neighbourhood lies in x because the intersection of neighbourhoods is the neighbourhood of myLor and x is closed under intersection. Each requested bit of the combined index is the Boolean disjunction of the two indices' bits, so it holds either by the head witness or by the recursive witness.

A position k lies in bitsList n if and only if the k-th bit of n is set.

Unfold bitsList and rewrite membership in a filtered initial segment. The forward direction is the filter predicate. The reverse direction adds the bound that a set bit lies strictly below n.

An element x of PN contains the neighbourhood nbhd n if and only if the complement of that neighbourhood is contained in elemSet x.

Rewrite the complement by its bit description. In the forward direction the same index n witnesses each of its set bits. In the reverse direction the combined-witness lemma, applied to bitsList n, produces one neighbourhood of x whose set bits cover those of n. That neighbourhood is contained in nbhd n, because a point it excludes has the corresponding bit of n either false, which is the required membership, or true, which contradicts the covering bit. Upward closure of x then yields membership of nbhd n.

If x is a computable element of the presentation PNpres, then membership in elemSet x is recursively enumerable.

Computability says that membership of nbhd n in x is recursively enumerable. The bit test on the two components of a paired number is recursively decidable by bitAt, its primitive recursiveness, and the correctness of bitAt. Conjoining that test with membership of the left component, and projecting away the pair, matches the existential definition of membership in elemSet after the unpairing identities.

A number k lies in the list decoded from bitsCode n N if and only if k is strictly below N and the k-th bit of n is set.

Recurse on N. At zero both sides simplify by the zero clauses of bitsCode and of list decoding. At a successor, split on whether the N-th bit of n is set. If it is, bitAt equals 1, the selector takes the cons branch, and decoding a successor code is cons; the inductive hypothesis and a split of the successor bound by omega give both directions. If it is not, bitAt differs from 1 and is at most 1, hence equals 0 by omega, the selector keeps the old accumulator, and the inductive hypothesis again splits the successor bound, with the new index contradicting the failed bit.

The step bitsStep is primitive recursive.

The three components of the packed state are primitive recursive, as are the bitAt test, the cons code given by pairing the counter with the accumulator and adding one, and the selector between that cons and the old accumulator. Packing the unchanged first component with the incremented counter and the selected accumulator is identified with bitsStep.

The first component of bitsStep s equals the first component of s.

Unfold bitsStep and cancel the outer pairing.

The counter component of bitsStep s is one greater than the counter component of s.

Unfold bitsStep and cancel the pairings that expose the counter.

The accumulator component of bitsStep s is the selector that conses the current counter onto the accumulator when the corresponding bit is set, and otherwise leaves the accumulator unchanged.

Unfold bitsStep and cancel the pairings that expose the accumulator.

Iterating bitsStep k times from the packing of n with a zero counter and a zero accumulator leaves n unchanged, sets the counter to k, and sets the accumulator to bitsCode n k.

Induct on k. The zero iteration is the identity on the initial packing, whose accumulator is the zero clause of bitsCode. At a successor, the three component lemmas for bitsStep transport the inductive state, and the accumulator equation is the defining clause of bitsCode.

The map sending a paired number to bitsCode of its two components is primitive recursive.

Primitive recursion starts from the packing of the left component with a zero counter and a zero accumulator, and steps by bitsStep on the accumulator, with the iteration count equal to the right component. The constant-iterator form of that recursion, read through the iteration specification of bitsStep, is the accumulator bitsCode.

If membership in elemSet x is recursively enumerable, then x is a computable element of PNpres.

Universal quantification of that predicate over the entries of a decoded list is recursively enumerable, and the diagonal sending n to bitsCode n n is primitive recursive. After composition, rewrite by the neighbourhood-membership criterion and the bit description of the complement. A set bit of n lies on that decoded diagonal list, using that a set bit is strictly below n, and conversely a decoded entry whose bit is set is a set bit of n.

An element x of PN is a computable element of PNpres if and only if membership in elemSet x is recursively enumerable.

One direction passes from a computable element to an enumerable positive set, and the other is the converse just proved.

If the first component of unnum c is a successor k + 1, then the second component is strictly smaller than c.

The round trip through numbering, rewritten by the successor hypothesis, says that numbering that successor with the second component recovers c. The strict growth of numbering in a positive left argument, together with omega, gives the decrease.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.capMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.bitAt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.cupMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.sumSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.orUpTo
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.plusIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.plusStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.plusMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.elemSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.bitsList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.bitsCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.bitsStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.tagStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.tagCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.tagOfBits
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.nextCellStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.unnumPair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.unnum1
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.unnum2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagRef
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagStep
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagVal
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.gMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.funMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.GraphIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.graphMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic.notation16
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.sumSet_mono
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.compl_subset_compl_of_subset
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.compl_inter_nbhd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_elemSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.GraphIdx_mono

@[expose] public section

/-!
# Exercise 7.23 (Scott 1981, PRG-19, §7) — completing the discussion of `PN`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Exercise 7.23.** Complete the discussion of `PN` of Example 7.8. Show that the combinators
> `fun` and `graph` of Exercise 5.14 are computable. Also do the same for `λx,y. x∩y`,
> `λx,y. x∪y`, and `λx,y. x+y`, where for `x,y ∈ PN` we define `x+y = {n+m ∣ n∈x and m∈y}`.
> What are the computable elements of `PN`?

**The key structural fact.** Write `E n := ℕ \ Example78.nbhd n = {k ∣ n.testBit k}` for the finite
set Scott's `nbhd n` excludes. `Example78.nbhd n ⊆ Example78.nbhd k ↔ E k ⊆ E n` (containment of
neighbourhoods *reverses* into containment of the excluded finite sets — this is exactly
`ComputablePresentation.incl_computable`, already proven generically for any
`ComputablePresentation`, applied to `Example78.PNpres`). Every binary combinator `λx,y. h(x,y)`
this exercise asks about turns out to test a *containment of finite sets* `E k ⊆ h(E n, E m)`, which
is exactly `nbhd n ⊆ nbhd k` (and/or `nbhd m ⊆ nbhd k`) reindexed — so **`∩`/`∪` are computable
reusing `incl_computable` directly, with no new bitwise/primitive-recursive machinery**: `∩` is the
conjunction of two containments (`Eₖ⊆Eₙ∩Eₘ ↔ Eₖ⊆Eₙ ∧ Eₖ⊆Eₘ`), and `∪` reduces to a single
containment against `myLor n m` (`Eₖ⊆Eₙ∪Eₘ ↔ Eₖ⊆E_{myLor n m} ↔ nbhd(myLor n m) ⊆ nbhd k`).
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-! ## `nbhd`-containment reverses into excluded-set containment -/

/-! ## `λx,y. x∩y` -/


/-! ## Bit-level utilities: `Nat.testBit` is primitive recursively decidable

Needed for `λx,y.x+y` (Minkowski sum) and for `fun`/`graph`, both of which test membership of a
*bit position* `k` of the excluded set `E_k` against a target condition. -/

/-- **Every set bit lies below the number itself.** If `n.testBit i = true` then `i < n` (since
`n ≥ 2^i > i`). -/
theorem lt_of_testBit_true {n i : ℕ} (h : n.testBit i = true) : i < n := by
  by_contra hle
  have hle' : n ≤ i := by omega
  have hlt : n < 2 ^ i := lt_of_le_of_lt hle' Nat.lt_two_pow_self
  rw [Nat.testBit_eq_false_of_lt hlt] at h
  exact absurd h (by decide)


theorem halfIter_succ (n k : ℕ) : halfIter n (k + 1) = halfIter (n / 2) k := by
  unfold halfIter; rw [Function.iterate_succ_apply]

theorem primrec_halfIter : Nat.Primrec (fun t => halfIter t.unpair.1 t.unpair.2) := by
  have hstep : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2 / 2) :=
    primrec_div2.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  refine (Nat.Primrec.prec primrec_id hstep).of_eq (fun t => ?_)
  simp only [Nat.unpaired, unpair_pair_snd]
  exact rec_const_iterate (fun x => x / 2) t.unpair.1 t.unpair.2


theorem primrec_bitAt : Nat.Primrec (fun t => bitAt t.unpair.1 t.unpair.2) :=
  primrec_mod2.comp primrec_halfIter

theorem bitAt_le_one (n k : ℕ) : bitAt n k ≤ 1 := by unfold bitAt; omega

/-- **Correctness of `bitAt`.** `bitAt n k = 1 ↔ n.testBit k = true`. -/
theorem bitAt_eq_one_iff (n k : ℕ) : bitAt n k = 1 ↔ n.testBit k = true := by
  induction k generalizing n with
  | zero =>
    show n % 2 = 1 ↔ n.testBit 0 = true
    rw [Nat.testBit_zero, decide_eq_true_iff]
  | succ k ih =>
    show halfIter n (k + 1) % 2 = 1 ↔ n.testBit (k + 1) = true
    rw [halfIter_succ, Nat.testBit_add_one]
    exact ih (n / 2)

/-! ## `λx,y. x∪y` -/


/-! ## `λx,y. x+y` (Minkowski sum)

Scott's `x + y = {n + m ∣ n ∈ x, m ∈ y}`. Written on excluded sets, `Eₙ + Eₘ` (Minkowski sum of two
*finite* sets) is again finite, and — since `a + b` ranges over `Eₙ + Eₘ` exactly when `a` ranges
over `Eₙ` and `b` over `Eₘ` — `Eₙ + Eₘ = ⋃ {a + Eₘ ∣ a ∈ Eₙ}`, a union of shifted copies of `Eₘ`, one
per set bit of `n`. This is computed by `plusIdx`, an iterative bitwise-OR fold (mirroring `myLor`)
of `m <<< a` over the set bits `a` of `n`. -/


/-- The excluded set of `nbhd n`, as a set of naturals: `(nbhd n)ᶜ = {k ∣ n.testBit k}`. -/
theorem compl_nbhd (n : ℕ) : (nbhd n)ᶜ = {k | n.testBit k = true} := by
  ext k; simp [nbhd]


/-! ## What are the computable elements of `PN`?

Every element `x` of `PN` is a downward-directed filter of the cofinite neighbourhoods `nbhd n`.
Write `elemSet x := ⋃ {Eₙ ∣ x.mem (nbhd n)}` for the (arbitrary) subset of `ℕ` it "positively
describes". Since `PN`'s neighbourhoods carry only *negative* information and any two are consistent
(`PN_consistent`), each single fact `x.mem (nbhd n)` is *generated* by finitely many of the positive
facts `k ∈ elemSet x` (`k ∈ Eₙ`) — combine their witnesses with `myLor` (`exists_combined_witness`) —
so `x.mem (nbhd n) ↔ Eₙ ⊆ elemSet x` (`nbhd_mem_iff_subset_elemSet`). This exhibits `PN` as
(isomorphic to) the classical powerset domain `(Set ℕ, ⊆)`, `x ↦ elemSet x`, and:

> **Theorem.** `x` is a computable element of `PN` iff `elemSet x` is a recursively enumerable
> subset of `ℕ` (`isComputableElement_iff_elemSet_re`).

I.e. **the computable elements of `PN` are exactly the recursively enumerable sets** — Scott's
headline fact about the powerset domain. -/


/-- **Finite covering (choice-free, structural induction on the witness list).** If every `k` in a
list `L` has *some* neighbourhood `nbhd m` of `x` with `m.testBit k`, a single `nbhd m₀ ∈ x` works for
all of `L` at once: combine the per-entry witnesses with `myLor` via `x.inter_mem`, one list entry at
a time. -/
theorem exists_combined_witness (x : PN.Element) :
    ∀ L : List ℕ, (∀ k ∈ L, ∃ m, x.mem (nbhd m) ∧ m.testBit k = true) →
      ∃ m₀, x.mem (nbhd m₀) ∧ ∀ k ∈ L, m₀.testBit k = true
  | [] => fun _ => ⟨0, nbhd_zero ▸ x.master_mem, by simp⟩
  | k :: L => by
    intro hL
    obtain ⟨mk, hmk, hbk⟩ := hL k List.mem_cons_self
    obtain ⟨m₀, hm₀, hall⟩ :=
      exists_combined_witness x L (fun j hj => hL j (List.mem_cons_of_mem k hj))
    refine ⟨myLor mk m₀, ?_, ?_⟩
    · rw [← nbhd_inter]; exact x.inter_mem hmk hm₀
    · intro j hj
      rw [myLor_eq_lor, Nat.testBit_lor, Bool.or_eq_true]
      rcases List.mem_cons.mp hj with rfl | hj
      · exact Or.inl hbk
      · exact Or.inr (hall j hj)


theorem mem_bitsList {n k : ℕ} : k ∈ bitsList n ↔ n.testBit k = true := by
  unfold bitsList
  rw [List.mem_filter, List.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨lt_of_testBit_true h, h⟩⟩

/-- **`x.mem (nbhd n) ↔ Eₙ ⊆ elemSet x`.** Neighbourhood-membership reduces to positive-information
containment: `n`'s excluded set must already be covered by `x`'s recorded information. -/
theorem nbhd_mem_iff_subset_elemSet (x : PN.Element) (n : ℕ) :
    x.mem (nbhd n) ↔ (nbhd n)ᶜ ⊆ elemSet x := by
  rw [compl_nbhd]
  constructor
  · intro hn k hk
    exact ⟨n, hn, hk⟩
  · intro hsub
    obtain ⟨m₀, hm₀, hall⟩ :=
      exists_combined_witness x (bitsList n) (fun k hk => hsub (mem_bitsList.mp hk))
    have hincl : nbhd m₀ ⊆ nbhd n := by
      intro k hk
      simp only [mem_nbhd] at hk ⊢
      cases hn2 : n.testBit k with
      | false => rfl
      | true =>
        have hcontra := hall k (mem_bitsList.mpr hn2)
        rw [hk] at hcontra
        exact absurd hcontra (by decide)
    exact x.up_mem hm₀ ⟨n, rfl⟩ hincl

/-- **`elemSet x` is r.e. when `x` is a computable element.** Direct: `k ∈ elemSet x ↔ ∃ n,
x.mem (nbhd n) ∧ n.testBit k`, an r.e. projection of the conjunction of an r.e. predicate and a
(`bitAt`-)decidable one. -/
theorem elemSet_re_of_isComputableElement {x : PN.Element} (hx : ComputableElement PNpres x) :
    REPred (fun k => k ∈ elemSet x) := by
  have hx' : REPred (fun n => x.mem (nbhd n)) := hx.out
  have hbit : RecDecidable (fun t : ℕ => t.unpair.1.testBit t.unpair.2 = true) :=
    ⟨fun t => bitAt t.unpair.1 t.unpair.2, primrec_bitAt, fun t => (bitAt_eq_one_iff _ _).symm⟩
  have hand : REPred (fun t : ℕ => x.mem (nbhd t.unpair.1) ∧ t.unpair.1.testBit t.unpair.2 = true) :=
    (hx'.comp Nat.Primrec.left).and hbit.re
  refine REPred.of_iff (fun k => ?_) hand.proj
  simp only [mem_elemSet, unpair_pair_fst, unpair_pair_snd]

/-! ### `bitsCode`: a primitive-recursive coding of "the list of set bits below `N`"

Needed for the converse computability direction: to invoke the generic closure
`REPred.forall_mem_decodeList`, the bounded conjunction `∀ k ∈ Eₙ, k ∈ A` must be phrased over a
*coded* list (`decodeList`), built by primitive recursion — not the plain `List.filter` form
`bitsList` above (which lives in `List ℕ`, outside the `Nat.Primrec` universe). `bitsCode` mirrors the
`plusStep`/`plusIdx` iteration pattern: it walks `k = 0, …, N-1`, consing `k` onto the running coded
list (`Nat.pair k acc + 1`, matching `decodeList`'s own `c + 1 ↦ c.unpair.1 :: decodeList c.unpair.2`)
exactly when `n.testBit k`. -/


theorem mem_decodeList_bitsCode (n : ℕ) :
    ∀ N k, k ∈ decodeList (bitsCode n N) ↔ k < N ∧ n.testBit k = true
  | 0, k => by simp [bitsCode, decodeList_zero]
  | N + 1, k => by
    show k ∈ decodeList (selectFn (bitAt n N) (Nat.pair N (bitsCode n N) + 1) (bitsCode n N)) ↔ _
    by_cases hbit : n.testBit N = true
    · rw [(bitAt_eq_one_iff n N).mpr hbit, selectFn_one, decodeList_succ, unpair_pair_fst,
        unpair_pair_snd, List.mem_cons, mem_decodeList_bitsCode n N k]
      constructor
      · rintro (rfl | ⟨hkN, hk⟩)
        · exact ⟨by omega, hbit⟩
        · exact ⟨by omega, hk⟩
      · rintro ⟨hkN1, hk⟩
        rcases (show k < N ∨ k = N by omega) with hkN | hkN
        · exact Or.inr ⟨hkN, hk⟩
        · exact Or.inl hkN
    · have hne1 : bitAt n N ≠ 1 := fun h => hbit ((bitAt_eq_one_iff n N).mp h)
      have hle := bitAt_le_one n N
      have hnbit : bitAt n N = 0 := by omega
      rw [hnbit, selectFn_zero, mem_decodeList_bitsCode n N k]
      constructor
      · rintro ⟨hkN, hk⟩
        exact ⟨Nat.lt_succ_of_lt hkN, hk⟩
      · rintro ⟨hkN1, hk⟩
        rcases (show k < N ∨ k = N by omega) with hkN | hkN
        · exact ⟨hkN, hk⟩
        · subst hkN; exact absurd hk hbit


theorem primrec_bitsStep : Nat.Primrec bitsStep := by
  have hn : Nat.Primrec (fun s : ℕ => s.unpair.1) := Nat.Primrec.left
  have hN : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hacc : Nat.Primrec (fun s : ℕ => s.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hbit : Nat.Primrec (fun s : ℕ => bitAt s.unpair.1 s.unpair.2.unpair.1) :=
    (primrec_bitAt.comp (hn.pair hN)).of_eq fun s => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hcons : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2 + 1) :=
    Nat.Primrec.succ.comp ((hN.pair hacc).of_eq fun _ => rfl)
  have hsel := primrec_selectFn hbit hcons hacc
  exact (hn.pair ((primrec_add₂ hN (Nat.Primrec.const 1)).pair hsel)).of_eq fun _ => rfl

theorem bitsStep_unpair11 (s : ℕ) : (bitsStep s).unpair.1 = s.unpair.1 := by
  unfold bitsStep; rw [unpair_pair_fst]

theorem bitsStep_unpair21 (s : ℕ) : (bitsStep s).unpair.2.unpair.1 = s.unpair.2.unpair.1 + 1 := by
  unfold bitsStep; rw [unpair_pair_snd, unpair_pair_fst]

theorem bitsStep_unpair22 (s : ℕ) : (bitsStep s).unpair.2.unpair.2 =
    selectFn (bitAt s.unpair.1 s.unpair.2.unpair.1)
      (Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2 + 1) s.unpair.2.unpair.2 := by
  unfold bitsStep; rw [unpair_pair_snd, unpair_pair_snd]

theorem bitsStep_iter_spec (n : ℕ) (k : ℕ) :
    (bitsStep^[k] (Nat.pair n (Nat.pair 0 0))).unpair.1 = n ∧
    (bitsStep^[k] (Nat.pair n (Nat.pair 0 0))).unpair.2.unpair.1 = k ∧
    (bitsStep^[k] (Nat.pair n (Nat.pair 0 0))).unpair.2.unpair.2 = bitsCode n k := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Function.iterate_zero, id_eq, unpair_pair_fst, unpair_pair_snd, bitsCode]
  | succ k ih =>
    obtain ⟨hn, hN, hacc⟩ := ih
    rw [Function.iterate_succ_apply']
    set s := bitsStep^[k] (Nat.pair n (Nat.pair 0 0))
    refine ⟨?_, ?_, ?_⟩
    · rw [bitsStep_unpair11, hn]
    · rw [bitsStep_unpair21, hN]
    · rw [bitsStep_unpair22, hn, hN, hacc]; rfl

theorem primrec_bitsCode : Nat.Primrec (fun t => bitsCode t.unpair.1 t.unpair.2) := by
  have hbase : Nat.Primrec (fun z : ℕ => Nat.pair z.unpair.1 (Nat.pair 0 0)) :=
    Nat.Primrec.left.pair ((Nat.Primrec.const 0).pair (Nat.Primrec.const 0))
  have hstep : Nat.Primrec (fun w : ℕ => bitsStep w.unpair.2.unpair.2) :=
    primrec_bitsStep.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hprec := Nat.Primrec.prec hbase hstep
  refine ((Nat.Primrec.right.comp Nat.Primrec.right).comp
    (hprec.comp (primrec_id.pair Nat.Primrec.right))).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rw [rec_const_iterate]
  exact (bitsStep_iter_spec t.unpair.1 t.unpair.2).2.2

/-- **`x` is a computable element when `elemSet x` is r.e.** The bounded conjunction `Eₙ ⊆ elemSet x`,
phrased over the coded list `bitsCode n n`, is r.e. by `REPred.forall_mem_decodeList`; by
`nbhd_mem_iff_subset_elemSet` this containment is exactly `x.mem (nbhd n)`. -/
theorem isComputableElement_of_elemSet_re {x : PN.Element} (hA : REPred (fun k => k ∈ elemSet x)) :
    ComputableElement PNpres x := by
  have hforall : REPred (fun c => ∀ e ∈ decodeList c, e ∈ elemSet x) := hA.forall_mem_decodeList
  have hcode : Nat.Primrec (fun n : ℕ => bitsCode n n) :=
    (primrec_bitsCode.comp (primrec_id.pair primrec_id)).of_eq fun n => by
      simp only [unpair_pair_fst, unpair_pair_snd, id_eq]
  constructor
  refine REPred.of_iff (fun n => ?_) (hforall.comp hcode)
  show x.mem (nbhd n) ↔ _
  rw [nbhd_mem_iff_subset_elemSet, compl_nbhd]
  constructor
  · intro hsub e he
    exact hsub ((mem_decodeList_bitsCode n n e).mp he).2
  · intro hall k hk
    exact hall k ((mem_decodeList_bitsCode n n k).mpr ⟨lt_of_testBit_true hk, hk⟩)

/-- **What are the computable elements of `PN`? — Exercise 7.23 (Scott 1981, PRG-19).** Exactly the
recursively enumerable subsets of `ℕ`, via the identification `x ↦ elemSet x` of `PN` with the
classical powerset domain `(Set ℕ, ⊆)`. -/
theorem isComputableElement_iff_elemSet_re (x : PN.Element) :
    ComputableElement PNpres x ↔ REPred (fun k => k ∈ elemSet x) :=
  ⟨elemSet_re_of_isComputableElement, isComputableElement_of_elemSet_re⟩

/-! ## `fun` and `graph` (Exercise 5.14) are computable

The last piece of Exercise 7.23. `PN.Element ≃ Set ℕ` via `elemSet` (established above), matching
Exercise 5.14's classical powerset model `Pω = (Set ℕ, ⊆)`. We reuse Exercise 5.14's combinators
`tag`/`Fun`/`Graph` verbatim, transported to the neighbourhood level by the same "reversal" idiom as
`capMap`/`cupMap`/`plusMap`: a neighbourhood-level combinator tests `Zᶜ ⊆ h(Xᶜ, Yᶜ)` for the
appropriate finite-set operation `h`. For `fun` this `h` is literally `Fun` (Exercise 5.14); `funMap`
is then the `curry` of the resulting two-variable map `gMap : PN × PN → PN`, so its computability is
*free* from `Theorem75.curry_isComputable` once `gMap` is shown computable. `graph` needs its own
direct construction (it does not factor through `curry`/`eval`), built from the canonical witness list
`decodeList (bitsCode j j)` for the excluded set `Eⱼ` of a domain neighbourhood `nbhd j`. -/

/-! ### `num`/`tag` are primitive recursive -/


/-! ### `unnum` is primitive recursive

`gMap`'s computability needs to *decode* `tag`: given `c ∈ Eₙ`, recover the unique `(ns, m)` with
`tag ns m = c` (uniqueness is `tag_injective`). Decoding peels one `unnum` layer at a time; `unnum`
itself is `nextCell` iterated (Exercise 5.13), so we first make `unnum` primitive recursive by the
same iterate-a-step-function device as `halfIter`/`bitsCode`/`plusIdx`. -/


/-! ### `untagRef`: the (non-primitive-recursive) structural inverse of `tag`

Reference decoder, by well-founded recursion peeling one `unnum` layer at a time (mirroring
`tag_surjective`'s existence proof, but now *computing* the witness); used only to state/prove
correctness of the primitive-recursive `untagList`/`untagVal` below. -/


/-- **`unnum`'s second component strictly decreases** when the first is a successor — the
decreasing measure for both `untagRef` (well-founded recursion) and `untagStep` (bounded
iteration) below. -/
theorem unnum_snd_lt_of_fst_succ {c k : ℕ} (h : (unnum c).1 = k + 1) : (unnum c).2 < c := by
  have heq : num (k + 1) (unnum c).2 = c := by
    have h' := numP_unnum c
    simpa [numP, h] using h'
  have hb := num_succ_left_gt k (unnum c).2
  omega

/-! ### `untagList`/`untagVal`: `untagRef`, made primitive recursive

Same "bounded iteration, no-op once done" device as `bitsCode`/`plusIdx`/`tagCode`: pack a state
`(code, done, revAcc, val)`; each step peels one `unnum` layer of `code` (consing onto `revAcc`,
coded via `appendStep`'s convention) until `unnum`'s first component is `0`, at which point `done`
is set and the state freezes. Since `code` strictly decreases every non-frozen step
(`unnum_snd_lt_of_fst_succ`), `c + 1` iterations always suffice to freeze starting from `code = c`. -/


/-! ### `gMap` is computable -/

/-! ### `fun`, via currying `gMap` -/


/-! ### `graph`, dually to `gMap` -/


/-! ### `graph` is computable -/
end DomainTheory.NeighbourhoodSystems.Exercise723
