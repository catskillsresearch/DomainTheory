module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.splitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtom

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

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

noncomputable def P0 : ComputablePresentation D :=
  P.reindexInvolutive (eIdx P) (eIdx_involutive P) (eIdx_primrec P)

@[simp] theorem P0_X (n : ℕ) : (P0 P).X n = P.X (eIdx P n) := rfl

noncomputable def datomDec : ℕ → ℕ := fun n => isOne ((DAtom_recDecidable (P0 P)).choose n)

noncomputable def atomUCodeState (t : ℕ) : ℕ :=
  t.unpair.2.rec (atomBase t.unpair.1) (fun y IH => atomStep (datomDec P) (Nat.pair t.unpair.1 (Nat.pair y IH)))

noncomputable def atomUCode (n k : ℕ) : ℕ := stateCode (atomUCodeState P (Nat.pair k n))

noncomputable def atomUNeg (n k : ℕ) : ℕ := stateNeg (atomUCodeState P (Nat.pair k n))

noncomputable def atomUPos (n k : ℕ) : ℕ := statePos (atomUCodeState P (Nat.pair k n))

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

theorem DAtom_cons_pos (Q : ComputablePresentation D) (i : ℕ) (pos neg : List ℕ) :
    DAtom Q (i :: pos) neg = idxSet Q.X i ∩ DAtom Q pos neg := by
  unfold DAtom; rw [IPos_cons, Set.inter_assoc]

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

theorem atomUCodeState_succ (k n : ℕ) :
    atomUCodeState P (Nat.pair k (n + 1)) =
      atomStep (datomDec P) (Nat.pair k (Nat.pair n (atomUCodeState P (Nat.pair k n)))) := by
  unfold atomUCodeState
  simp only [unpair_pair_fst, unpair_pair_snd]

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

theorem atomUEmpty_succ (k n : ℕ) :
    atomUEmpty P (n + 1) k =
      selectFn ((k / 2 ^ n) % 2)
        (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)))
        (datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1))) := by
  unfold atomUEmpty
  rw [atomUPos_succ, atomUNeg_succ]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hbit | hbit <;>
    simp only [hbit, selectFn_zero, selectFn_one]

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

theorem mem (n k : ℕ) : U.mem (UX (atomUCode P n k)) := U_mem_UX _
end atomUCode

theorem atomUEmpty_congr {n k k' : ℕ} (h : ∀ i < n, deltaOf k i = deltaOf k' i) :
    atomUEmpty P n k = atomUEmpty P n k' := by
  obtain ⟨hpos, hneg, -⟩ := atomUCodeState_congr P h
  unfold atomUEmpty
  rw [hpos, hneg]

theorem atomUEmpty_zero_or_one (n k : ℕ) : atomUEmpty P n k = 0 ∨ atomUEmpty P n k = 1 := by
  have h := datomDec_le_one P (Nat.pair (atomUPos P n k) (atomUNeg P n k))
  unfold atomUEmpty
  omega

end DomainTheory.NeighbourhoodSystems
