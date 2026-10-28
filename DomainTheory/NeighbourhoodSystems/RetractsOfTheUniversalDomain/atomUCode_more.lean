module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomUCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DprimeUPresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtom
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.QPairCodes
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive
open AtomCode

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

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
      rw [atomUCode.succ, atomUCode.succ, hpos, hneg, hcode]

      rcases Bool.eq_false_or_eq_true (deltaOf k n) with h1 | h1
      ·
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
      ·
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
        (Set.inter_subset_inter (atomUCode.subset P hk) (atomUCode.subset P hk')) hd

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

theorem DAtom_union (i : ℕ) (pos neg : List ℕ) :
    DAtom (P0 P) pos neg = DAtom (P0 P) (i :: pos) neg ∪ DAtom (P0 P) pos (i :: neg) := by
  ext m
  simp only [mem_DAtom, Set.mem_union, List.mem_cons, forall_eq_or_imp]
  by_cases hm : (P0 P).X m ⊆ (P0 P).X i <;> tauto

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem datomDec_eq_zero (posC negC : ℕ) (h : DAtom (P0 P) (decodeList posC) (decodeList negC) ≠ ∅) :
    datomDec P (Nat.pair posC negC) = 0 := by
  have hle := datomDec_le_one P (Nat.pair posC negC)
  have hne : datomDec P (Nat.pair posC negC) ≠ 1 := fun he => h ((datomDec_spec P posC negC).mp he)
  omega

theorem deltaOf_mod_two_pow_of_lt {k n i : ℕ} (hi : i < n) :
    deltaOf (k % 2 ^ n) i = deltaOf k i := by
  rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.testBit_mod_two_pow]
  simp [hi]

theorem atomUCodeState_congr_twin (n k : ℕ) :
    atomUPos P n (k % 2 ^ n + 2 ^ n) = atomUPos P n k ∧
      atomUNeg P n (k % 2 ^ n + 2 ^ n) = atomUNeg P n k ∧
      atomUCode P n (k % 2 ^ n + 2 ^ n) = atomUCode P n k := by
  have hagree : ∀ i < n, deltaOf (k % 2 ^ n + 2 ^ n) i = deltaOf k i := by
    intro i hi
    rw [deltaOf_add_two_pow_of_lt _ hi, deltaOf_mod_two_pow_of_lt hi]
  exact atomUCodeState_congr P hagree

theorem eq_of_deltaOf_agree_of_lt_two_pow {n i j : ℕ} (hi : i < 2 ^ n) (hj : j < 2 ^ n)
    (hagree : ∀ l < n, deltaOf i l = deltaOf j l) : i = j := by
  apply Nat.eq_of_testBit_eq
  intro l
  rw [← deltaOf_eq_testBit, ← deltaOf_eq_testBit]
  rcases Nat.lt_or_ge l n with hl | hl
  · exact hagree l hl
  · have hile : 2 ^ n ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
    rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.testBit_lt_two_pow (hi.trans_le hile),
      Nat.testBit_lt_two_pow (hj.trans_le hile)]

end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem primrec_datomDec : Nat.Primrec (datomDec P) :=
  (primrec_isOne.comp (DAtom_recDecidable (P0 P)).choose_spec.1).of_eq fun _ => rfl
end

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem primrec_atomUCodeState : Nat.Primrec (atomUCodeState P) :=
  (Nat.Primrec.prec primrec_atomBase (primrec_atomStep (primrec_datomDec P))).of_eq fun _t => rfl

theorem primrec_atomUCode : Nat.Primrec (fun t : ℕ => atomUCode P t.unpair.1 t.unpair.2) :=
  (primrec_stateCode.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

theorem primrec_atomUNeg : Nat.Primrec (fun t : ℕ => atomUNeg P t.unpair.1 t.unpair.2) :=
  (primrec_stateNeg.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

theorem primrec_atomUPos : Nat.Primrec (fun t : ℕ => atomUPos P t.unpair.1 t.unpair.2) :=
  (primrec_statePos.comp (primrec_atomUCodeState P |>.comp
    (Nat.Primrec.right.pair Nat.Primrec.left))).of_eq fun _ => rfl

theorem primrec_atomUEmpty : Nat.Primrec (fun t : ℕ => atomUEmpty P t.unpair.1 t.unpair.2) :=
  ((primrec_datomDec P).comp ((primrec_atomUPos P).pair (primrec_atomUNeg P))).of_eq
    fun _ => rfl

end

end DomainTheory.NeighbourhoodSystems
