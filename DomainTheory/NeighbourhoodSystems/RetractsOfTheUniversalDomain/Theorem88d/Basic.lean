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

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

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

theorem atomUPos_zero (k : ℕ) : atomUPos P 0 k = 0 := by
  simp [atomUPos, atomUCodeState, atomBase]

theorem atomUNeg_zero (k : ℕ) : atomUNeg P 0 k = 0 := by
  simp [atomUNeg, atomUCodeState, atomBase]

theorem atomUCode_zero (k : ℕ) : atomUCode P 0 k = UmasterIdx := by
  simp [atomUCode, atomUCodeState, atomBase]

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

end DomainTheory.NeighbourhoodSystems
