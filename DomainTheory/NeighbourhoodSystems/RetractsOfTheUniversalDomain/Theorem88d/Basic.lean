/-ai
The extracted decider reads 1 on a pair of list codes exactly when the D-atom of the re-pointed presentation on the decoded lists is empty.

Unfold the decider and rewrite a reading of 1 by the zero-one test. The specification of the chosen D-atom decider, after unpairing, is that biconditional.

The extracted decider is at most 1.

Unfold it. The zero-one wrapper is at most 1.

Prepending an index to the positive list intersects the D-atom with the index set of that index.

Unfold the atom, rewrite the positive part by its cons clause, and reassociate the intersection.

Prepending an index to the negative list intersects the D-atom with the complement of the index set of that index.

Extensionality: a point satisfies the positive constraints and avoids every negative index, including the new one, exactly when it avoids the new index set, satisfies the positive constraints, and avoids the remaining negative indices.

The packed state at depth n+1 for a bit-source is the one-step transition applied to the state at depth n.

Unfold the state recursion and simplify the unpairing.

The unconsumed remainder at depth n is the bit-source divided by two to the power n.

Induct on the depth. At depth 0 the base state keeps the bit-source. At a successor, unfold the step, apply the inductive hypothesis, and combine the successive divisions into division by the next power of two.

The bit predicate reads true at position i exactly when the bit-source divided by two to the power i is odd.

Unfold the definition and simplify.

The positive code at depth n+1 selects, by the bit at n, either the code with n prepended or the previous positive code.

Unfold the positive code, replace the state by its successor, unfold the step, and simplify. The remainder at depth n is the shifted bit-source.

The negative code at depth n+1 selects, by the same bit, either the previous negative code or the code with n prepended.

The same unfolding, reading the negative component of the packed step.

The generated atom of the index sets of the re-pointed enumeration, taken against the universe along the bits of a bit-source, equals the D-atom of the re-pointed presentation on the decoded positive and negative codes.

Induct on the depth. At depth 0 both sides are the full set of indices. At a successor, if the bit is true the generated atom meets the index set of the current index, the positive code prepends that index, and the cons clause for a positive constraint matches after the intersection is commuted. If the bit is false the generated atom meets the complement of that index set, the negative code prepends the index, and the cons clause for a negative constraint matches the same way.

The emptiness flag reads 1 exactly when that D-atom is empty.

This is the specification of the decider on the pair of the two codes.

The emptiness flag reads 1 exactly when the generated atom along the bits of the bit-source is empty.

Rewrite by the previous equivalence and by the agreement of the generated atom with the D-atom.

The emptiness flag reads 0 exactly when that generated atom is nonempty.

The flag is at most 1. A reading of 0 cannot be the reading 1 that emptiness would force, and any reading other than 0 is 1, which is emptiness.

At depth 0 the positive code is 0.

Simplify the base state.

At depth 0 the negative code is 0.

Simplify the base state.

At depth 0 the U-code is the master index of the universal system.

Simplify the base state.

The U-code at depth n+1 is the nested selection on the bit at n and on the two one-step emptiness checks: each bit selects 0 when its own refinement is empty, and otherwise selects the old code or the corresponding split of the old code according to the other check.

Unfold the code and the two list codes, replace the state by its successor, unfold the step, and simplify the projections. The remainder at depth n supplies the bit.

The emptiness flag at depth n+1 equals the positive-refinement check when the bit is 1 and the negative-refinement check when the bit is 0.

Unfold the flag, rewrite both list codes by their successor equations, and simplify on the two possible values of the bit.

Bit-sources that agree on the first n bits have the same positive code, the same negative code, and the same U-code at depth n.

Induct on the depth. At depth 0 all three components are independent of the bit-source. At a successor the inductive hypothesis gives agreement at the previous depth, and the bits at that depth agree because the sign predicates agree. The three successor formulas then agree.

The generated atom at depth n+1 is contained in the generated atom at depth n.

The successor atom is the left factor of an intersection.

If the emptiness flag reads 1 at depth n, it reads 1 at depth n+1.

Rewrite both readings as emptiness of generated atoms. The successor atom is contained in the earlier atom, so emptiness persists.

If the emptiness flag reads 0 at depth n+1, it reads 0 at depth n.

Otherwise the flag at depth n, being at most 1, would read 1, and the monotonicity of the flag would force the successor to read 1.

Once the emptiness flag reads 1, the U-code at the next depth is 0.

Emptiness of the D-atom gives emptiness of both one-step refinements, since each is an intersection with that atom, so both emptiness checks read 1. The successor formula for the code then selects 0 on either bit.

If the emptiness flag reads 0 at depth n+1, the neighbourhood of the new U-code is contained in the neighbourhood of the old one.

Rewrite the flag and the code by their successor formulas. On bit 0 the negative-refinement check reads 0, and the positive-refinement check either reads 0, so the code is the right split and that neighbourhood is contained in the old one, or reads 1, so the code is unchanged. On bit 1 the positive-refinement check reads 0, and the negative-refinement check either reads 0, so the code is the left split, or reads 1, so the code is unchanged.

If two bit-sources are both non-junk at depth n and disagree on some bit below n, their universal neighbourhoods are disjoint.

Induct on the depth. Depth 0 admits no bit below it. At depth n+1, if the sources agree below n, the disagreement is at bit n, and congruence identifies the depth-n data. The two selected emptiness checks then read 0, and the two codes are the two sides of one split, which are disjoint. If the sources already disagree below n, the inductive hypothesis gives disjointness at depth n, both flags there read 0, and both neighbourhoods shrink, so the intersection at the next depth stays empty.

The bit predicate is the standard test of a binary digit.

This is the symmetry of the equation identifying the bit predicate with the test bit.

Adding two to the power n does not change bits strictly below n.

Rewrite both sides as test bits and apply the lemma on adding a higher power of two.

If m is strictly below two to the power n, then m plus that power has bit n set.

Rewrite the bit predicate as a test bit. Adding the power sets that bit, and m itself has the bit unset.

The encoding of any finite sign prefix is strictly below two to the power of its length.

Induct on the length. The empty prefix encodes as 0. At a successor the inductive bound and the positivity of the previous power give the bound whether or not the new sign contributes that power, because the next power is twice the previous one.

The encoding of a sign sequence reproduces that sequence on every bit strictly below the encoded length.

Induct on the length. At a successor, split on the new sign. When it contributes the power of two, a lower bit is preserved by adding that power and agrees by the inductive hypothesis, while the top bit is set. When the added term vanishes, a lower bit agrees by the inductive hypothesis, and the top bit of a number below that power is unset.

For every depth n there is an index i below two to the power n such that the bit-source i plus that power is non-junk at depth n+1.

Let the sign at j record whether n belongs to the index set of j. The sign at n is true, because n belongs to its own index set, so the generated atom at depth n+1 is the atom at depth n met with that index set. The index n belongs to the atom at depth n and to its own index set, so the atom at depth n+1 is nonempty. Encode the first n signs. The sum of that code with two to the power n lies in the required range and agrees with the signs through bit n: below n by preservation under the encoding and under adding the power, and at n because the sum sets that bit. Congruence of generated atoms carries the nonempty atom to this bit-source, and the flag reads 0 exactly when that atom is nonempty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.unionUX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.wY
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.wState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateRem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.statePos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateNeg
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomBase
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.datomDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCodeState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUPos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUNeg
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.deltaOf
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUEmpty
import all DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.encodeBits
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFoldStep
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFold
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.YseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Yc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateRem_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.statePos_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateNeg_packState
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateCode_packState

@[expose] public section

/-!
# Theorem 8.8(b), Part 7 — a genuinely computable back-and-forth construction

Part 6 (`Theorem88c.lean`) showed Theorem 8.8(a)'s *classical* subsystem `D' = DprimeU` (built via
`splitChoice`) is effectively given as an abstract domain in its own right. That is **not** enough
for Part 7: `IsComputableMap` needs the *cross*-relation between `D'` and `U` — concretely,
`Yidx e n ⊆ UX m` — to be recursively enumerable, and `Yidx e n`'s actual position among `U`'s
rational intervals is, by construction, whatever `Classical.choice` happened to pick. There is no
effective handle on it at all, so no relation mentioning it can be shown r.e.

This file therefore builds a **fresh, genuinely computable** back-and-forth construction,
replacing Theorem 8.8(a)'s abstract, `Set`-valued splitting recursion (`Theorem88.lean`'s
`atomU`/`split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ`) with one that works **natively on `U`-codes**
throughout, so that at every step there is an actual `ℕ`-code in hand — never a `Set ℚ` value
conjured by choice.

## Why the original `atomUCode`/`splitEff` plan failed, and how this one differs

The design pitfall recorded in `HANDOFF.md` (2026-07-02) was: to reuse `Theorem88.lean`'s *generic*
apparatus, `split` must be a **total function of `Set`s** (`Set α → Set ℚ → Set α → Set ℚ × Set ℚ`).
Given only a *set* `B`, there is no way to effectively recover "the" code for it (`canonCode` is not
unique-per-set, so `splitULeft`/`splitURight` — which key off a code's specific first interval — can
give different answers for different codes of the same set). Any attempt to define `splitEff` as a
function of `B : Set ℚ` alone (e.g. via `Classical.choice`/`Nat.find` to pick a representative code)
is therefore not provably the same split an independently-built code tracker would compute.

**This file sidesteps the problem instead of solving it**: it never builds a `Set`-valued `split`
function at all, and does not reuse `Theorem88.lean`'s generic `atomU`/`Yseq`/`transfer_*` machinery.
Instead, the entire back-and-forth recursion is defined **natively as a `Nat.Primrec` function of
`(depth, sign-sequence-code)`**, carrying an explicit `U`-code as part of its state from the very
first step — so "which code represents `B`" is never a question, only ever "the code my own
recursion already computed". The three ingredients, all already built:

* Part 4 (`SplitU.lean`): `splitULeft`/`splitURight`, a deterministic, `Nat.Primrec` midpoint split
  of *any* `U`-code, with `UX_splitULeft`/`UX_splitURight` holding **unconditionally** (no side
  conditions on the input code) — this is what makes composing it across recursion steps trivial.
* Part 5 (`DAtomDecidable.lean`): `DAtom_recDecidable (P0 P)`, deciding whether a finite Boolean
  atom-constraint on `D`'s neighbourhoods is empty, extracted as a genuine `Nat.Primrec` function.
* `DAtom`'s monotonicity under adding constraints (`DAtom (i :: pos) neg ⊆ DAtom pos neg`, via
  `IPos_cons`): once a `(pos, neg)`-atom is detected empty, every further extension of it is
  automatically detected empty too, by the *same* decider, with **no extra "already empty" flag
  needed** in the recursion state.

## Status

This file lays the **foundational recursion** (`atomUCode`, `Nat.Primrec`), its **per-step `D`-side
correctness** (`genAtom_atomUCode`), and now **Theorem 8.8(b)(vii)(1), the full `atomUCode`
invariant**: `atomUCode_mem` (validity, unconditional — `UX` is a total surjection onto `U`'s
neighbourhoods, so this needs no emptiness hypothesis at all, unlike `Theorem88.lean`'s `atomU`) and
`atomUCode_disjoint` (atoms for bit-sources disagreeing below depth `n`, and *both* still `D`-side
non-empty, are `U`-side disjoint). The restriction to non-empty atoms is unavoidable and harmless:
`atomUCode_eq_zero_of_empty` shows a once-empty atom's code freezes at the junk value `0` forever, so
every junk atom aliases to the same `UX 0` — disjointness genuinely fails there, but `(vii)(2)`'s
`YseqCode` filters junk `k`'s out of its union, so this restricted invariant is exactly what is
needed downstream.

The remaining assembly (Part 7b: a `Yseq`-analogue as a *union* over `2ⁿ` such atoms, disjointness,
subset/intersection transfer, `D''`'s `NeighborhoodSystem`/`ComputablePresentation`,
`D ≅ᴰ D''`/`D'' ◁ U`; Part 7c: `IsComputableMap` itself) is **not yet done** — see `HANDOFF.md` for
the detailed continuation plan. Nothing in this file is a placeholder or `sorry`; everything proved
here is a real, checked, reusable building block for that continuation.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-! ## Union of two `U`-codes via `appendCode` (list concatenation, up to order) -/


/-! ## The code-native atom recursion

Fix `P : ComputablePresentation D` and work relative to `P0 P` (Part 6b's re-pointed presentation,
`(P0 P).X 0 = D.master`). The recursion state at depth `n`, for a fixed bit-source `k` (`k`'s bit
`y` records the sign `δ y ∈ {true, false}` of the depth-`y` step), is packed as

`pair remK (pair posC (pair negC uCode))`

where `remK` is the *unconsumed* suffix of `k` (peeled one bit at a time via `/2`, avoiding the need
for a general `Nat.Primrec` division-by-`2^y`), `posC`/`negC` are `encodeList`-style codes for the
accumulated positive/negative index lists (Part 6c's `posnegList`, built by **prepending** instead
of appending — harmless, since `DAtom`/`IPos` only ever care about list *membership*), and `uCode`
is the `U`-code of the matching `U`-side atom (meaningful only when the `D`-side atom is
non-empty). -/

section AtomCode

variable {E : NeighborhoodSystem α} (Q : ComputablePresentation E)


end AtomCode

/-! ## Instantiating at `datomDec := DAtom_recDecidable (P0 P)`'s extracted decider -/

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


theorem datomDec_spec (posC negC : ℕ) :
    datomDec P (Nat.pair posC negC) = 1 ↔ DAtom (P0 P) (decodeList posC) (decodeList negC) = ∅ := by
  unfold datomDec
  rw [isOne_eq_one_iff]
  have h := (DAtom_recDecidable (P0 P)).choose_spec.2 (Nat.pair posC negC)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

theorem datomDec_le_one (n : ℕ) : datomDec P n ≤ 1 := by unfold datomDec; exact isOne_le_one _


/-! ## Per-step correctness: the `D`-side atom is tracked exactly -/

/-- `DAtom` gains a positive constraint by intersecting with `idxSet`, prepended. -/
theorem DAtom_cons_pos (Q : ComputablePresentation D) (i : ℕ) (pos neg : List ℕ) :
    DAtom Q (i :: pos) neg = idxSet Q.X i ∩ DAtom Q pos neg := by
  unfold DAtom; rw [IPos_cons, Set.inter_assoc]

/-- `DAtom` gains a negative constraint by intersecting with the complement of `idxSet`, prepended. -/
theorem DAtom_cons_neg (Q : ComputablePresentation D) (j : ℕ) (pos neg : List ℕ) :
    DAtom Q pos (j :: neg) = (Set.univ \ idxSet Q.X j) ∩ DAtom Q pos neg := by
  ext m
  simp only [mem_DAtom, List.mem_cons, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_univ, true_and,
    mem_idxSet]
  constructor
  · rintro ⟨hpos, hneg⟩
    exact ⟨hneg j (Or.inl rfl), hpos, fun i hi => hneg i (Or.inr hi)⟩
  · rintro ⟨hj, hpos, hneg⟩
    exact ⟨hpos, fun i hi => hi.elim (fun h => h ▸ hj) (hneg i)⟩


/-- **Unfolding `atomUCodeState` one step.** -/
theorem atomUCodeState_succ (k n : ℕ) :
    atomUCodeState P (Nat.pair k (n + 1)) =
      atomStep (datomDec P) (Nat.pair k (Nat.pair n (atomUCodeState P (Nat.pair k n)))) := by
  unfold atomUCodeState
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- The unconsumed bit-source at depth `n` is exactly `k / 2 ^ n` (peeled one bit at a time). -/
theorem stateRem_atomUCodeState (k n : ℕ) : stateRem (atomUCodeState P (Nat.pair k n)) = k / 2 ^ n := by
  induction n with
  | zero => simp [atomUCodeState, atomBase]
  | succ n ih =>
    rw [atomUCodeState_succ]
    unfold atomStep
    simp only [wY, wState, unpair_pair_fst, unpair_pair_snd, stateRem_packState, ih,
      Nat.div_div_eq_div_mul, ← pow_succ]

theorem deltaOf_eq_true_iff (k i : ℕ) : deltaOf k i = true ↔ (k / 2 ^ i) % 2 = 1 := by
  unfold deltaOf; simp

/-- `atomUPos`/`atomUNeg` step by prepending the new index `n` on whichever side `deltaOf k n`
selects, exactly mirroring `genAtom`'s own step. -/
theorem atomUPos_succ (k n : ℕ) :
    atomUPos P (n + 1) k =
      selectFn ((k / 2 ^ n) % 2) (Nat.pair n (atomUPos P n k) + 1) (atomUPos P n k) := by
  unfold atomUPos
  rw [atomUCodeState_succ]
  unfold atomStep
  simp only [wY, wState, unpair_pair_fst, unpair_pair_snd, statePos_packState,
    stateRem_atomUCodeState]

theorem atomUNeg_succ (k n : ℕ) :
    atomUNeg P (n + 1) k =
      selectFn ((k / 2 ^ n) % 2) (atomUNeg P n k) (Nat.pair n (atomUNeg P n k) + 1) := by
  unfold atomUNeg
  rw [atomUCodeState_succ]
  unfold atomStep
  simp only [wY, wState, unpair_pair_fst, unpair_pair_snd, stateNeg_packState,
    stateRem_atomUCodeState]

/-- **Per-step `D`-side correctness.** The accumulated `(pos, neg)` code pair at depth `n`, for
bit-source `k`, tracks exactly the same atom as `genAtom (idxSet (e P)) Set.univ (deltaOf k) n`. -/
theorem genAtom_atomUCode (k : ℕ) :
    ∀ n, genAtom (idxSet (e P)) Set.univ (deltaOf k) n
      = DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) := by
  intro n
  induction n with
  | zero =>
    simp [genAtom, atomUPos, atomUNeg, atomUCodeState, atomBase, DAtom, decodeList_zero, IPos_nil]
  | succ n ih =>
    rcases Bool.eq_false_or_eq_true (deltaOf k n) with hδ | hδ
    · have hbit1 : (k / 2 ^ n) % 2 = 1 := (deltaOf_eq_true_iff k n).mp hδ
      have hstep : genAtom (idxSet (e P)) Set.univ (deltaOf k) (n + 1) =
          genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩ idxSet (e P) n := by
        show genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩
          (if deltaOf k n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [hδ]
      rw [hstep, ih, atomUPos_succ, atomUNeg_succ, hbit1, selectFn_one, selectFn_one,
        decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_pos, Set.inter_comm]
    · have hbit0 : (k / 2 ^ n) % 2 = 0 := by
        rcases Nat.eq_zero_or_pos ((k / 2 ^ n) % 2) with h | h
        · exact h
        · exact absurd ((deltaOf_eq_true_iff k n).mpr (by omega)) (by simp [hδ])
      have hstep : genAtom (idxSet (e P)) Set.univ (deltaOf k) (n + 1) =
          genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩ (Set.univ \ idxSet (e P) n) := by
        show genAtom (idxSet (e P)) Set.univ (deltaOf k) n ∩
          (if deltaOf k n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
        simp [hδ]
      rw [hstep, ih, atomUPos_succ, atomUNeg_succ, hbit0, selectFn_zero, selectFn_zero,
        decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_neg, Set.inter_comm]

/-! ## Theorem 8.8(b)(vii)(1) — the `atomUCode` invariant

Unlike `Theorem88.lean`'s `atomU` (valued in genuine `Set ℚ`, where `∅` is an honest value),
`UX : ℕ → Set ℚ` is a **total surjection onto `U`'s neighbourhoods** (`U_mem_UX`, unconditional:
`canonCode`'s degenerate-input fallback is `U.master`, never `∅`) — no code represents the empty
set. So the right invariant here is *not* `atomU_invariant`'s emptiness-matching clause "(■)"
verbatim; instead:

* **validity** holds completely for free, for *every* code (`U_mem_UX`), empty match or not;
* **disjointness** only holds, and only needs to hold, between two atoms that are *both* still
  `D`-side non-empty (`atomUEmpty = 0`) — once a bit-source's atom goes empty its code is frozen at
  the junk value `0` forever (`atomUCode_eq_zero_of_empty` below), and *all* junk atoms alias to the
  same `UX 0`, so disjointness genuinely fails between two junk atoms (or junk vs. non-junk) and must
  be excluded; `(vii)(2)`'s `YseqCode` filters junk `k`'s out of its union, so this restricted
  disjointness is exactly what is needed downstream. -/


theorem atomUEmpty_eq_one_iff (n k : ℕ) :
    atomUEmpty P n k = 1 ↔ DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) = ∅ :=
  datomDec_spec P _ _

/-- **`atomUEmpty` reads off `genAtom`'s own emptiness**, via `genAtom_atomUCode`. -/
theorem atomUEmpty_eq_one_iff_genAtom (n k : ℕ) :
    atomUEmpty P n k = 1 ↔ genAtom (idxSet (e P)) Set.univ (deltaOf k) n = ∅ := by
  rw [atomUEmpty_eq_one_iff, ← genAtom_atomUCode]

theorem atomUEmpty_eq_zero_iff_genAtom (n k : ℕ) :
    atomUEmpty P n k = 0 ↔ genAtom (idxSet (e P)) Set.univ (deltaOf k) n ≠ ∅ := by
  have hle : atomUEmpty P n k ≤ 1 := datomDec_le_one P _
  have h1 := atomUEmpty_eq_one_iff_genAtom P n k
  constructor
  · intro h0 hempty; exact absurd (h1.mpr hempty) (by omega)
  · intro hne; by_contra h0; exact hne (h1.mp (by omega))

/-! ### The zero-depth base case, unconditionally (no dependence on `k`) -/

theorem atomUPos_zero (k : ℕ) : atomUPos P 0 k = 0 := by
  simp [atomUPos, atomUCodeState, atomBase]

theorem atomUNeg_zero (k : ℕ) : atomUNeg P 0 k = 0 := by
  simp [atomUNeg, atomUCodeState, atomBase]

theorem atomUCode_zero (k : ℕ) : atomUCode P 0 k = UmasterIdx := by
  simp [atomUCode, atomUCodeState, atomBase]

/-! ### Unfolding the `U`-side code one step

Mirrors `atomUPos_succ`/`atomUNeg_succ`: `atomUCode P (n+1) k` is a nested `selectFn` on the actual
bit `(k / 2^n) % 2` and the *two* hypothetical extension-emptiness checks (whichever the actual bit
picks decides `0`-vs-carry-vs-split; the *other* is exactly the sibling's own `atomUEmpty` at depth
`n+1`, which is what powers the disjointness argument below). -/
theorem atomUCode_succ (k n : ℕ) :
    atomUCode P (n + 1) k =
      selectFn ((k / 2 ^ n) % 2)
        (selectFn (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k))) 0
          (selectFn (datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)))
            (atomUCode P n k) (splitULeft (atomUCode P n k))))
        (selectFn (datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1))) 0
          (selectFn (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)))
            (atomUCode P n k) (splitURight (atomUCode P n k)))) := by
  unfold atomUCode atomUPos atomUNeg
  rw [atomUCodeState_succ]
  unfold atomStep
  simp only [wY, wState, unpair_pair_fst, unpair_pair_snd, stateCode_packState,
    stateRem_atomUCodeState]

/-- The two hypothetical checks appearing in `atomUCode_succ` are exactly `atomUEmpty` at depth
`n + 1`, evaluated at whichever of the two bit-sources through `n` realizes each hypothesis. In
particular, for the *actual* bit-source `k` itself: whichever branch `(k/2^n)%2` selects reproduces
`atomUEmpty P (n+1) k` verbatim. -/
theorem atomUEmpty_succ (k n : ℕ) :
    atomUEmpty P (n + 1) k =
      selectFn ((k / 2 ^ n) % 2)
        (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)))
        (datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1))) := by
  unfold atomUEmpty
  rw [atomUPos_succ, atomUNeg_succ]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hbit | hbit <;>
    simp only [hbit, selectFn_zero, selectFn_one]

/-! ### Congruence: the recursion depends only on `deltaOf k`'s first `n` bits -/

/-- **Congruence for the whole packed triple**: bit-sources agreeing on `deltaOf` below `n` produce
identical `(pos, neg, code)` triples at depth `n` — the code-level analogue of `genAtom_congr`/
`atomU_congr`, proved jointly (the three components interact through `atomUCode_succ`'s two
`datomDec` checks, which read `atomUPos`/`atomUNeg` at depth `n`). -/
theorem atomUCodeState_congr {n : ℕ} :
    ∀ {k k' : ℕ}, (∀ i < n, deltaOf k i = deltaOf k' i) →
      atomUPos P n k = atomUPos P n k' ∧ atomUNeg P n k = atomUNeg P n k' ∧
        atomUCode P n k = atomUCode P n k' := by
  induction n with
  | zero =>
    intro k k' _
    exact ⟨(atomUPos_zero P k).trans (atomUPos_zero P k').symm,
      (atomUNeg_zero P k).trans (atomUNeg_zero P k').symm,
      (atomUCode_zero P k).trans (atomUCode_zero P k').symm⟩
  | succ n ih =>
    intro k k' h
    obtain ⟨ihpos, ihneg, ihcode⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hbit : (k / 2 ^ n) % 2 = (k' / 2 ^ n) % 2 := by
      have hh := h n (Nat.lt_succ_self n)
      rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one (k' / 2 ^ n) with h2 | h2 <;>
          simp_all [deltaOf]
    refine ⟨?_, ?_, ?_⟩
    · rw [atomUPos_succ, atomUPos_succ, ihpos, hbit]
    · rw [atomUNeg_succ, atomUNeg_succ, ihneg, hbit]
    · rw [atomUCode_succ, atomUCode_succ, ihpos, ihneg, ihcode, hbit]

/-! ### Validity: every code is a genuine `U`-neighbourhood, unconditionally -/

/-! ### Junk propagates: once empty, `atomUCode` is frozen at `0` forever -/

theorem genAtom_succ_subset (k n : ℕ) :
    genAtom (idxSet (e P)) Set.univ (deltaOf k) (n + 1) ⊆
      genAtom (idxSet (e P)) Set.univ (deltaOf k) n :=
  Set.inter_subset_left

theorem atomUEmpty_mono {n k : ℕ} (h : atomUEmpty P n k = 1) : atomUEmpty P (n + 1) k = 1 := by
  rw [atomUEmpty_eq_one_iff_genAtom] at h ⊢
  exact Set.subset_eq_empty (genAtom_succ_subset P k n) h

theorem atomUEmpty_zero_of_succ {n k : ℕ} (h : atomUEmpty P (n + 1) k = 0) : atomUEmpty P n k = 0 := by
  by_contra hne
  have hle := datomDec_le_one P (Nat.pair (atomUPos P n k) (atomUNeg P n k))
  have h1 : atomUEmpty P n k = 1 := by unfold atomUEmpty at hne hle ⊢; omega
  exact absurd (atomUEmpty_mono P h1) (by omega)

/-- **Junk is frozen at `0`.** Once a bit-source's `D`-side atom is empty, its `U`-code stays `0`
forever after (both hypothetical continuations of an already-empty atom are themselves empty, so
`atomUCode_succ`'s outer `selectFn` always lands on its `0` branch). -/
theorem atomUCode_eq_zero_of_empty {n k : ℕ} (h : atomUEmpty P n k = 1) :
    atomUCode P (n + 1) k = 0 := by
  have hemp : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) = ∅ :=
    (atomUEmpty_eq_one_iff P n k).mp h
  have hI : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 1 := by
    refine (datomDec_spec P _ _).mpr ?_
    rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_pos]
    exact Set.subset_empty_iff.mp (hemp ▸ Set.inter_subset_right)
  have hJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 1 := by
    refine (datomDec_spec P _ _).mpr ?_
    rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, DAtom_cons_neg]
    exact Set.subset_empty_iff.mp (hemp ▸ Set.inter_subset_right)
  rw [atomUCode_succ, hI, hJ]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hbit | hbit <;>
    simp [hbit, selectFn_zero, selectFn_one]

/-- **Monotonicity**: as long as the depth-`(n+1)` atom is still non-empty, its `U`-code's
neighbourhood shrinks from (or coincides with) the depth-`n` one — either the "carry unchanged"
branch fires (equality) or a genuine `splitULeft`/`splitURight` fires (strict `⊆`, `UX_splitULeft`/
`UX_splitURight`). Mirrors `split_fst_subset`/`split_snd_subset` from the abstract `Theorem88.lean`
account, but unconditionally true here since `splitULeft`/`splitURight` need no side hypotheses. -/
theorem atomUCode_subset {n k : ℕ} (h : atomUEmpty P (n + 1) k = 0) :
    UX (atomUCode P (n + 1) k) ⊆ UX (atomUCode P n k) := by
  have hemp := h
  rw [atomUEmpty_succ] at hemp
  rw [atomUCode_succ]
  set posC := atomUPos P n k
  set negC := atomUNeg P n k
  set c := atomUCode P n k
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hbit | hbit
  · simp only [hbit, selectFn_zero] at hemp ⊢
    rw [hemp, selectFn_zero]
    have hle := datomDec_le_one P (Nat.pair (Nat.pair n posC + 1) negC)
    rcases (by omega : datomDec P (Nat.pair (Nat.pair n posC + 1) negC) = 0 ∨
        datomDec P (Nat.pair (Nat.pair n posC + 1) negC) = 1) with h2 | h2
    · rw [h2, selectFn_zero, UX_splitURight]; exact Set.inter_subset_left
    · rw [h2, selectFn_one]
  · simp only [hbit, selectFn_one] at hemp ⊢
    rw [hemp, selectFn_zero]
    have hle := datomDec_le_one P (Nat.pair posC (Nat.pair n negC + 1))
    rcases (by omega : datomDec P (Nat.pair posC (Nat.pair n negC + 1)) = 0 ∨
        datomDec P (Nat.pair posC (Nat.pair n negC + 1)) = 1) with h2 | h2
    · rw [h2, selectFn_zero, UX_splitULeft]; exact Set.inter_subset_left
    · rw [h2, selectFn_one]

/-! ### Disjointness -/

/-- **The core `(vii)(1)` result**: at every depth `n`, atoms for bit-sources disagreeing somewhere
below `n` are disjoint on the `U`-side, *provided both are still `D`-side non-empty*. Proved by
induction on `n`, mirroring `atomU_invariant`'s disjointness clause: either the disagreement is
already below `n - 1` (recurse, then shrink both sides via `atomUCode_subset`), or it is exactly at
the last bit (use `atomUCodeState_congr` to identify the shared depth-`(n-1)` ancestor, then
`splitU_disjoint`, since both survive to depth `n` iff that step was a genuine split). -/
theorem atomUCode_disjoint :
    ∀ n k k', atomUEmpty P n k = 0 → atomUEmpty P n k' = 0 → (∃ i < n, deltaOf k i ≠ deltaOf k' i) →
      UX (atomUCode P n k) ∩ UX (atomUCode P n k') = ∅ := by
  intro n
  induction n with
  | zero => intro k k' _ _ ⟨i, hi, _⟩; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro k k' hk hk' ⟨i, hi, hne⟩
    by_cases hagree : ∀ j < n, deltaOf k j = deltaOf k' j
    · have hδn : deltaOf k n ≠ deltaOf k' n := by
        intro heq
        apply hne
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact hagree i hi'
        · exact heq
      obtain ⟨hpos, hneg, hcode⟩ := atomUCodeState_congr P hagree
      rw [atomUCode_succ, atomUCode_succ, hpos, hneg, hcode]
      -- `Bool.eq_false_or_eq_true` enumerates `true` before `false`.
      rcases Bool.eq_false_or_eq_true (deltaOf k n) with h1 | h1
      · -- `deltaOf k n = true`: `k` takes bit `1`, so `deltaOf k' n` must be `false`.
        have hbitk : (k / 2 ^ n) % 2 = 1 := (deltaOf_eq_true_iff k n).mp h1
        have h2 : deltaOf k' n = false := by
          rcases Bool.eq_false_or_eq_true (deltaOf k' n) with h2 | h2
          · exact absurd (h1.trans h2.symm) hδn
          · exact h2
        have hbitk' : (k' / 2 ^ n) % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (k' / 2 ^ n) with hh | hh
          · exact hh
          · exact absurd ((deltaOf_eq_true_iff k' n).mpr hh) (by simp [h2])
        have hkI : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 0 := by
          have h := hk; rw [atomUEmpty_succ, hbitk, selectFn_one] at h; exact h
        have hk'J : datomDec P (Nat.pair (atomUPos P n k') (Nat.pair n (atomUNeg P n k') + 1)) = 0 := by
          have h := hk'; rw [atomUEmpty_succ, hbitk', selectFn_zero] at h; exact h
        rw [hpos, hneg] at hkI
        simp only [hbitk, hbitk', selectFn_zero, selectFn_one, hkI, hk'J]
        exact splitU_disjoint (atomUCode P n k')
      · -- `deltaOf k n = false`: `k` takes bit `0`, so `deltaOf k' n` must be `true`.
        have hbitk : (k / 2 ^ n) % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hh | hh
          · exact hh
          · exact absurd ((deltaOf_eq_true_iff k n).mpr hh) (by simp [h1])
        have h2 : deltaOf k' n = true := by
          rcases Bool.eq_false_or_eq_true (deltaOf k' n) with h2 | h2
          · exact h2
          · exact absurd (h1.trans h2.symm) hδn
        have hbitk' : (k' / 2 ^ n) % 2 = 1 := (deltaOf_eq_true_iff k' n).mp h2
        have hkJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 0 := by
          have h := hk; rw [atomUEmpty_succ, hbitk, selectFn_zero] at h; exact h
        have hk'I : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k') + 1) (atomUNeg P n k')) = 0 := by
          have h := hk'; rw [atomUEmpty_succ, hbitk', selectFn_one] at h; exact h
        rw [hpos, hneg] at hkJ
        simp only [hbitk, hbitk', selectFn_zero, selectFn_one, hkJ, hk'I]
        exact (Set.inter_comm _ _).trans (splitU_disjoint (atomUCode P n k'))
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hd : UX (atomUCode P n k) ∩ UX (atomUCode P n k') = ∅ :=
        ih k k' (atomUEmpty_zero_of_succ P hk) (atomUEmpty_zero_of_succ P hk') ⟨j, hj, hjne⟩
      exact Set.subset_eq_empty
        (Set.inter_subset_inter (atomUCode_subset P hk) (atomUCode_subset P hk')) hd

/-! ## Theorem 8.8(b)(vii)(2) — `YseqCode`, Scott's `Yₙ` coded

Scott's `Yₙ` (`Theorem88.lean`'s `Yseq`) is the union, over the `2ⁿ` depth-`(n+1)` atoms with bit
`n` forced `1`, of the "+"-piece chosen at that step. Here that union is built **as a `Nat.Primrec`
fold over `U`-codes** (`yFold`/`YseqCode`), skipping any bit-source whose `D`-side atom is already
junk (`atomUEmpty = 1`) — since a junk atom's code is *frozen at the aliasing value `0`*
(`atomUCode_eq_zero_of_empty`), and `UX 0 = U.master` (`canonCode`'s degenerate-input fallback), a
naive unfiltered union would corrupt every depth's result to `U.master` outright. -/

/-! ### Bit-level arithmetic for `deltaOf`, via `Nat.testBit`

`deltaOf` is definitionally `Nat.testBit` in disguise (`Nat.testBit_eq_decide_div_mod_eq`), so every
fact below is a direct transcription of a core `Nat.testBit` lemma about `2ⁿ`-shifted/masked
naturals — no bespoke bit-manipulation induction is needed. -/

theorem deltaOf_eq_testBit (k i : ℕ) : deltaOf k i = k.testBit i :=
  Nat.testBit_eq_decide_div_mod_eq.symm

/-- Adding `2ⁿ` never disturbs bits strictly below `n`. -/
theorem deltaOf_add_two_pow_of_lt {n : ℕ} (m : ℕ) {i : ℕ} (hi : i < n) :
    deltaOf (m + 2 ^ n) i = deltaOf m i := by
  rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.add_comm, Nat.testBit_two_pow_add_gt hi]

/-- Adding `2ⁿ` to an `m < 2ⁿ` sets exactly bit `n` (no carry beyond it). -/
theorem deltaOf_two_pow_add_self {n m : ℕ} (hm : m < 2 ^ n) : deltaOf (m + 2 ^ n) n = true := by
  rw [deltaOf_eq_testBit, Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm]
  rfl

/-! ### `encodeBits`: realizing a prescribed finite bit-prefix as an explicit `ℕ`

Purely a `Prop`-level existence tool (never claimed `Nat.Primrec`): given *any* `δ : ℕ → Bool`,
`encodeBits δ n < 2ⁿ` is a bit-source whose first `n` bits match `δ`'s. Used once, below, to turn
the *abstract* nonemptiness fact "every index's own atom is nonempty" into a concrete witness
bit-source for `yFold`'s search range. -/


private theorem encodeBits_lt (δ : ℕ → Bool) : ∀ n, encodeBits δ n < 2 ^ n
  | 0 => by simp [encodeBits]
  | n + 1 => by
      have ih := encodeBits_lt δ n
      have hp := Nat.two_pow_pos n
      show encodeBits δ n + (if δ n then 2 ^ n else 0) < 2 ^ (n + 1)
      rw [pow_succ]
      rcases Bool.eq_false_or_eq_true (δ n) with hδn | hδn <;> simp [hδn] <;> omega

private theorem deltaOf_encodeBits (δ : ℕ → Bool) :
    ∀ n i, i < n → deltaOf (encodeBits δ n) i = δ i
  | n + 1, i, hi => by
      have hlt := encodeBits_lt δ n
      show deltaOf (encodeBits δ n + (if δ n then 2 ^ n else 0)) i = δ i
      rcases Bool.eq_false_or_eq_true (δ n) with hδn | hδn
      · have hval : encodeBits δ n + (if δ n then 2 ^ n else 0) = encodeBits δ n + 2 ^ n := by
          rw [hδn]; simp
        rw [hval]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · rw [deltaOf_add_two_pow_of_lt _ hi']; exact deltaOf_encodeBits δ n i hi'
        · rw [deltaOf_two_pow_add_self hlt, hδn]
      · have hval : encodeBits δ n + (if δ n then 2 ^ n else 0) = encodeBits δ n := by
          rw [hδn]; simp
        rw [hval]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact deltaOf_encodeBits δ n i hi'
        · rw [deltaOf_eq_testBit, Nat.testBit_lt_two_pow hlt, hδn]

/-! ### Existence: some bit-source among `{i + 2ⁿ ∣ i < 2ⁿ}` is always `D`-side non-empty

Mirrors `Theorem88a.lean`'s `Yidx_nonempty` (every index `n` witnesses its own `idxSet e n`'s
self-membership, `self_mem_idxSet`), transported to the bit-source encoding via `encodeBits`. -/

theorem exists_atomUEmpty_zero (n : ℕ) : ∃ i < 2 ^ n, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 := by
  classical
  set δ0 : ℕ → Bool := fun j => decide (n ∈ idxSet (e P) j) with hδ0def
  have hδ0n : δ0 n = true := by
    show decide (n ∈ idxSet (e P) n) = true
    rw [decide_eq_true_iff]; exact self_mem_idxSet (e P) n
  have hstep : genAtom (idxSet (e P)) Set.univ δ0 (n + 1) =
      genAtom (idxSet (e P)) Set.univ δ0 n ∩ idxSet (e P) n := by
    show genAtom (idxSet (e P)) Set.univ δ0 n ∩
      (if δ0 n then idxSet (e P) n else Set.univ \ idxSet (e P) n) = _
    simp [hδ0n]
  have hxn : n ∈ genAtom (idxSet (e P)) Set.univ δ0 n :=
    genAtom_self (idxSet (e P)) Set.univ (Set.mem_univ n) n
  have hmem : n ∈ genAtom (idxSet (e P)) Set.univ δ0 n ∩ idxSet (e P) n :=
    ⟨hxn, self_mem_idxSet (e P) n⟩
  have hAne : genAtom (idxSet (e P)) Set.univ δ0 (n + 1) ≠ ∅ := by
    rw [hstep]; exact Set.Nonempty.ne_empty ⟨n, hmem⟩
  set m0 := encodeBits δ0 n with hm0def
  have hm0lt : m0 < 2 ^ n := encodeBits_lt δ0 n
  refine ⟨m0, hm0lt, ?_⟩
  rw [atomUEmpty_eq_zero_iff_genAtom]
  have hagree : ∀ j < n + 1, deltaOf (m0 + 2 ^ n) j = δ0 j := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · rw [deltaOf_add_two_pow_of_lt _ hj']; exact deltaOf_encodeBits δ0 n j hj'
    · rw [deltaOf_two_pow_add_self hm0lt, hδ0n]
  rw [genAtom_congr (idxSet (e P)) Set.univ hagree]
  exact hAne

/-! ### `atomUEmpty` is `Nat.Primrec` -/

/-! ### The union fold: `yFoldStep`/`yFold`

`yFoldStep` is written as a function of a **single** packed argument `w = pair n (pair i acc)`
(mirroring `atomStep`'s own convention), so that feeding it directly into `Nat.Primrec.prec` needs
no further unpair/pair bookkeeping. -/


/-! ### Correctness: `yFold`'s "found" flag and running union, by induction on `N` -/

/-! ### `YseqCode`: assembling the fold at `N = 2ⁿ` -/


/-! ### The closed form: `YseqCode` recovers the "+"-piece of the atom recursion

Mirrors `Theorem88.lean`'s `split_fst_eq_inter_Yseq`: the "+"-branch chosen at depth `n` by the
atom recursion is exactly the intersection of the depth-`n` atom with `YseqCode`. Pairwise
disjointness (`atomUCode_disjoint`) is what rules out any *other* atom leaking a point into
`UX (YseqCode P n)` that isn't already forced into this one. -/

end DomainTheory.NeighbourhoodSystems
