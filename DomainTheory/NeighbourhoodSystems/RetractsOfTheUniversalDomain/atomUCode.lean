module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.splitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtom

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **Swap `0` and `P.masterIdx`.** A primitive-recursive involution on `ℕ` re-pointing whichever
index `P.masterIdx` names `D`'s master neighbourhood to sit at index `0` instead, leaving every
other index fixed. -/
def eIdx (n : ℕ) : ℕ :=
  if n = 0 then P.masterIdx else if n = P.masterIdx then 0 else n

theorem eIdx_involutive : Function.Involutive (eIdx P) := by
  intro n
  unfold eIdx
  split_ifs with h0 hm hm' hm'' hm''' <;> simp_all

theorem eIdx_primrec : Nat.Primrec (eIdx P) := by
  have hc0 : Nat.Primrec (fun n => isZero n) := primrec_isZero
  have hcm : Nat.Primrec (fun n : ℕ => isZero ((n - P.masterIdx) + (P.masterIdx - n))) :=
    primrec_isZero.comp
      (primrec_add₂ (primrec_sub₂ primrec_id (Nat.Primrec.const P.masterIdx))
        (primrec_sub₂ (Nat.Primrec.const P.masterIdx) primrec_id))
  have hinner : Nat.Primrec (fun n : ℕ =>
      selectFn (isZero ((n - P.masterIdx) + (P.masterIdx - n))) 0 n) :=
    primrec_ite hcm (Nat.Primrec.const 0) primrec_id
  refine (primrec_ite hc0 (Nat.Primrec.const P.masterIdx) hinner).of_eq (fun n => ?_)
  rcases (show isZero n = 0 ∨ isZero n = 1 from by have := isZero_le_one n; omega) with h0 | h0
  · rw [h0, selectFn_zero]
    have hn0 : n ≠ 0 := by intro h; subst h; unfold isZero at h0; omega
    rcases (show isZero ((n - P.masterIdx) + (P.masterIdx - n)) = 0 ∨
        isZero ((n - P.masterIdx) + (P.masterIdx - n)) = 1 from
        by have := isZero_le_one ((n - P.masterIdx) + (P.masterIdx - n)); omega) with h1 | h1
    · rw [h1, selectFn_zero]
      have hnm : n ≠ P.masterIdx := by intro h; subst h; unfold isZero at h1; omega
      unfold eIdx
      rw [ite_eq_right hn0, ite_eq_right hnm]
    · rw [h1, selectFn_one]
      have hnm : n = P.masterIdx := by unfold isZero at h1; omega
      unfold eIdx
      rw [ite_eq_right hn0, ite_eq_left hnm]
  · rw [h0, selectFn_one]
    have hn0 : n = 0 := by unfold isZero at h0; omega
    unfold eIdx
    rw [ite_eq_left hn0]

/-- **The re-pointed presentation `P₀`**: `P`'s enumeration reindexed by `eIdx`, so that
`P₀.X 0 = D.master`. Built via `ComputablePresentation.reindexInvolutive`, so every one of Scott's
structural fields — in particular the two deciders `interEq_computable`/`cons_computable` needed
for `DAtom_recDecidable` — transfers automatically, with no need to redo Part 5's work. -/
noncomputable def P0 : ComputablePresentation D :=
  P.reindexInvolutive (eIdx P) (eIdx_involutive P) (eIdx_primrec P)

@[simp] theorem P0_X (n : ℕ) : (P0 P).X n = P.X (eIdx P n) := rfl

/-- **The extracted `D`-atom-emptiness decider for `P0 P`.** Obtained non-constructively
(`Classical.choice`, via `RecDecidable`'s bare existential) from `DAtom_recDecidable (P0 P)`; the
resulting *function* is exactly as computable as any other `Nat.Primrec` function in this
codebase — only *naming* it needs choice, mirroring `DprimeUPresentation`'s own `noncomputable`.
Wrapped in `isOne` so the result is *literally* `{0,1}`-valued (not just "`= 1` iff ..."): `(vii)(1)`'s
`selectFn`-based case analysis on `emptyI`/`emptyJ` needs the *exact* value `0` on the false side, not
merely `≠ 1` (`selectFn`, unlike a genuine `if`, is only well-behaved on a literal `0`/`1` condition). -/
noncomputable def datomDec : ℕ → ℕ := fun n => isOne ((DAtom_recDecidable (P0 P)).choose n)

/-- **The full state recursion**, packing `atomBase`/`atomStep (datomDec P)` via `Nat.Primrec.prec`:
`atomUCodeState P (pair k n)` is the depth-`n` state for bit-source `k`. -/
noncomputable def atomUCodeState (t : ℕ) : ℕ :=
  t.unpair.2.rec (atomBase t.unpair.1) (fun y IH => atomStep (datomDec P) (Nat.pair t.unpair.1 (Nat.pair y IH)))

/-- **The depth-`n` `U`-side code**, for bit-source `k` (meaningful exactly when the matching
`D`-side atom, `DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k))`, is
non-empty — see `genAtom_atomUCode` below). -/
noncomputable def atomUCode (n k : ℕ) : ℕ := stateCode (atomUCodeState P (Nat.pair k n))

/-- **The depth-`n` accumulated negative-index code**, for bit-source `k`. -/
noncomputable def atomUNeg (n k : ℕ) : ℕ := stateNeg (atomUCodeState P (Nat.pair k n))

/-- **The depth-`n` accumulated positive-index code**, for bit-source `k`. -/
noncomputable def atomUPos (n k : ℕ) : ℕ := statePos (atomUCodeState P (Nat.pair k n))

/-- **`D`-side atom emptiness at depth `n`, for bit-source `k`** — `1` iff the accumulated
`(pos, neg)` constraint pair already denotes the empty `D`-index atom. -/
noncomputable def atomUEmpty (n k : ℕ) : ℕ := datomDec P (Nat.pair (atomUPos P n k) (atomUNeg P n k))

theorem datomDec_spec (posC negC : ℕ) :
    datomDec P (Nat.pair posC negC) = 1 ↔ DAtom (P0 P) (decodeList posC) (decodeList negC) = ∅ := by
  unfold datomDec
  rw [isOne_eq_one_iff]
  have h := (DAtom_recDecidable (P0 P)).choose_spec.2 (Nat.pair posC negC)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

theorem datomDec_le_one (n : ℕ) : datomDec P n ≤ 1 := by unfold datomDec; exact isOne_le_one _

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

theorem atomUEmpty_eq_one_iff (n k : ℕ) :
    atomUEmpty P n k = 1 ↔ DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) = ∅ :=
  datomDec_spec P _ _

theorem atomUPos_zero (k : ℕ) : atomUPos P 0 k = 0 := by
  simp [atomUPos, atomUCodeState, atomBase]

theorem atomUNeg_zero (k : ℕ) : atomUNeg P 0 k = 0 := by
  simp [atomUNeg, atomUCodeState, atomBase]

namespace atomUCode

theorem zero (k : ℕ) : atomUCode P 0 k = UmasterIdx := by
  simp [atomUCode, atomUCodeState, atomBase]

theorem succ (k n : ℕ) :
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


end atomUCode

/-- The two hypothetical checks appearing in `atomUCode.succ` are exactly `atomUEmpty` at depth
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

/-- **Congruence for the whole packed triple**: bit-sources agreeing on `deltaOf` below `n` produce
identical `(pos, neg, code)` triples at depth `n` — the code-level analogue of `genAtom_congr`/
`atomU_congr`, proved jointly (the three components interact through `atomUCode.succ`'s two
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
      (atomUCode.zero P k).trans (atomUCode.zero P k').symm⟩
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
    · rw [atomUCode.succ, atomUCode.succ, ihpos, ihneg, ihcode, hbit]


namespace atomUCode
/-- **Junk is frozen at `0`.** Once a bit-source's `D`-side atom is empty, its `U`-code stays `0`
forever after (both hypothetical continuations of an already-empty atom are themselves empty, so
`succ`'s outer `selectFn` always lands on its `0` branch). -/
theorem eq_zero_of_empty {n k : ℕ} (h : atomUEmpty P n k = 1) :
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
  rw [succ, hI, hJ]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hbit | hbit <;>
    simp [hbit, selectFn_zero, selectFn_one]

/-- **Monotonicity**: as long as the depth-`(n+1)` atom is still non-empty, its `U`-code's
neighbourhood shrinks from (or coincides with) the depth-`n` one — either the "carry unchanged"
branch fires (equality) or a genuine `splitULeft`/`splitURight` fires (strict `⊆`, `UX_splitULeft`/
`UX_splitURight`). Mirrors `split_fst_subset`/`split_snd_subset` from the abstract `Theorem88.lean`
account, but unconditionally true here since `splitULeft`/`splitURight` need no side hypotheses. -/
theorem subset {n k : ℕ} (h : atomUEmpty P (n + 1) k = 0) :
    UX (atomUCode P (n + 1) k) ⊆ UX (atomUCode P n k) := by
  have hemp := h
  rw [atomUEmpty_succ] at hemp
  rw [succ]
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


/-- **Validity**, the free half of the invariant: `UX` never needs an emptiness hypothesis at all. -/
theorem mem (n k : ℕ) : U.mem (UX (atomUCode P n k)) := U_mem_UX _
end atomUCode

end DomainTheory.NeighbourhoodSystems
