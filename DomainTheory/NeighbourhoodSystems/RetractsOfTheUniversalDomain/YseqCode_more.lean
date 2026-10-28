module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.YseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomUCode_more
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.QPairCodes

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive
open AtomCode

section
open NeighborhoodSystem Domain.Recursive
variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem primrec_yFoldStep : Nat.Primrec (yFoldStep P) := by
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h2n : Nat.Primrec (fun w : ℕ => 2 ^ w.unpair.1) := primrec_two_pow hn
  have hk : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1 + 2 ^ w.unpair.1) :=
    primrec_add₂ hi h2n
  have hn1 : Nat.Primrec (fun w : ℕ => w.unpair.1 + 1) := Nat.Primrec.succ.comp hn
  have hempty : Nat.Primrec (fun w : ℕ =>
      atomUEmpty P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)) :=
    ((primrec_atomUEmpty P).comp (hn1.pair hk)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hcode : Nat.Primrec (fun w : ℕ =>
      atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)) :=
    ((primrec_atomUCode P).comp (hn1.pair hk)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hfound : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp hacc
  have hval : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp hacc
  have hunion : Nat.Primrec (fun w : ℕ => unionUX w.unpair.2.unpair.2.unpair.2
      (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1))) :=
    (primrec_unionUX.comp (hval.pair hcode)).of_eq
      fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hinner : Nat.Primrec (fun w : ℕ => selectFn w.unpair.2.unpair.2.unpair.1
      (Nat.pair 1 (unionUX w.unpair.2.unpair.2.unpair.2
        (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1))))
      (Nat.pair 1 (atomUCode P (w.unpair.1 + 1) (w.unpair.2.unpair.1 + 2 ^ w.unpair.1)))) :=
    primrec_selectFn hfound
      ((Nat.Primrec.const 1).pair hunion)
      ((Nat.Primrec.const 1).pair hcode)
  exact (primrec_selectFn hempty hacc hinner).of_eq fun w => by unfold yFoldStep; simp only []

theorem primrec_yFold : Nat.Primrec (fun t : ℕ => yFold P t.unpair.1 t.unpair.2) :=
  (Nat.Primrec.prec (Nat.Primrec.const (Nat.pair 0 0)) (primrec_yFoldStep P)).of_eq fun _ => rfl

theorem primrec_YseqCode : Nat.Primrec (YseqCode P) := by
  have h2n : Nat.Primrec (fun n : ℕ => 2 ^ n) := primrec_two_pow Nat.Primrec.id
  refine (Nat.Primrec.right.comp ((primrec_yFold P).comp (Nat.Primrec.id.pair h2n))).of_eq
    fun n => ?_
  show ((yFold P (Nat.pair n (2 ^ n)).unpair.1 (Nat.pair n (2 ^ n)).unpair.2)).unpair.2 = YseqCode P n
  rw [unpair_pair_fst, unpair_pair_snd]
  rfl

theorem UX_unionUX (n m : ℕ) : UX (unionUX n m) = UX n ∪ UX m := by
  have hmem : U.mem (presentedIntervals (decodeQPairList (Domain.Recursive.appendCode (canonCode n) (canonCode m)))) := by
    rw [presentedIntervals_decodeQPairList_appendCode]; exact U_mem_union_UX n m
  show presentedIntervals (decodeQPairList (canonCode (unionUX n m))) = UX n ∪ UX m
  unfold unionUX
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hmem,
    presentedIntervals_decodeQPairList_appendCode]
  rfl

theorem yFold_mem_iff (n : ℕ) :
    ∀ N, (yFold P n N).unpair.1 = 1 →
      ∀ z : ℚ, z ∈ UX (yFold P n N).unpair.2 ↔
        ∃ i < N, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 ∧ z ∈ UX (atomUCode P (n + 1) (i + 2 ^ n)) := by
  intro N
  induction N with
  | zero => intro h; simp [yFold_zero] at h
  | succ N ih =>
    intro hfound1 z
    rw [yFold_succ, yFoldStep_eq] at hfound1 ⊢
    rcases atomUEmpty_zero_or_one P (n + 1) (N + 2 ^ n) with h0 | h1
    · rw [h0, selectFn_zero] at hfound1 ⊢
      rcases Nat.eq_zero_or_pos (yFold P n N).unpair.1 with hf0 | hfpos
      · rw [show (yFold P n N).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_snd]
        constructor
        · intro hz; exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact absurd ((yFold_found_iff P n N).mpr ⟨i, hi', hie⟩) (by rw [hf0]; omega)
          · exact hz
      · have hf1 : (yFold P n N).unpair.1 = 1 := by
          have := yFold_found_le_one P n N; omega
        rw [hf1, selectFn_one, unpair_pair_snd, UX_unionUX, Set.mem_union, ih hf1 z]
        constructor
        · rintro (⟨i, hi, hie, hz⟩ | hz)
          · exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
          · exact ⟨N, Nat.lt_succ_self N, h0, hz⟩
        · rintro ⟨i, hi, hie, hz⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
          · exact Or.inl ⟨i, hi', hie, hz⟩
          · exact Or.inr hz
    · rw [h1, selectFn_one] at hfound1 ⊢
      rw [ih hfound1 z]
      constructor
      · rintro ⟨i, hi, hie, hz⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie, hz⟩
      · rintro ⟨i, hi, hie, hz⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie, hz⟩
        · exact absurd hie (by omega)

theorem yFold_two_pow_found (n : ℕ) : (yFold P n (2 ^ n)).unpair.1 = 1 :=
  (yFold_found_iff P n (2 ^ n)).mpr (exists_atomUEmpty_zero P n)

theorem mem_UX_YseqCode_iff (n : ℕ) (z : ℚ) :
    z ∈ UX (YseqCode P n) ↔
      ∃ i < 2 ^ n, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 ∧ z ∈ UX (atomUCode P (n + 1) (i + 2 ^ n)) :=
  yFold_mem_iff P n (2 ^ n) (yFold_two_pow_found P n) z

theorem atomUCode_disjoint_YseqCode_of_posTwin_empty {n k' : ℕ} (hk' : atomUEmpty P n k' = 0)
    (hjunk : atomUEmpty P (n + 1) (k' % 2 ^ n + 2 ^ n) = 1) :
    UX (atomUCode P n k') ∩ UX (YseqCode P n) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨hzB, hzY⟩
  obtain ⟨i, hilt, hie, hz⟩ := (mem_UX_YseqCode_iff P n z).mp hzY
  set j := k' % 2 ^ n with hjdef
  have hjlt : j < 2 ^ n := Nat.mod_lt k' (Nat.two_pow_pos n)
  have hk'j : ∀ l < n, deltaOf k' l = deltaOf j l := by
    intro l hl; rw [hjdef, deltaOf_mod_two_pow_of_lt hl]
  by_cases hij : i = j
  · rw [hij] at hie; exact absurd hie (by omega)
  · have hdisagree : ∃ l < n, deltaOf (i + 2 ^ n) l ≠ deltaOf k' l := by
      by_contra hcon
      push Not at hcon
      apply hij
      apply eq_of_deltaOf_agree_of_lt_two_pow hilt hjlt
      intro l hl
      have h1 : deltaOf (i + 2 ^ n) l = deltaOf i l := deltaOf_add_two_pow_of_lt _ hl
      have h2 := hcon l hl
      rw [h1] at h2
      exact h2.trans (hk'j l hl)
    obtain ⟨l, hl, hlne⟩ := hdisagree
    have hd : UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k') = ∅ :=
      atomUCode_disjoint P n (i + 2 ^ n) k' (atomUEmpty_zero_of_succ P hie) hk' ⟨l, hl, hlne⟩
    have hzB' : z ∈ UX (atomUCode P n (i + 2 ^ n)) := atomUCode.subset P hie hz
    have hzmem : z ∈ UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k') := ⟨hzB', hzB⟩
    rw [hd] at hzmem
    exact absurd hzmem (Set.mem_empty_iff_false z).mp

theorem atomUCode_succ_true {k n : ℕ} (hne : atomUEmpty P (n + 1) k = 0)
    (hδ : deltaOf k n = true) :
    UX (atomUCode P (n + 1) k) = UX (atomUCode P n k) ∩ UX (YseqCode P n) := by
  set j := k % 2 ^ n with hjdef
  have hjlt : j < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
  have hagree : ∀ i < n + 1, deltaOf k i = deltaOf (j + 2 ^ n) i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · rw [deltaOf_add_two_pow_of_lt _ hi', hjdef, deltaOf_mod_two_pow_of_lt hi']
    · rw [deltaOf_two_pow_add_self hjlt, hδ]
  obtain ⟨hpos_eq, hneg_eq, hcode_eq⟩ := atomUCodeState_congr P hagree
  have hempty_eq : atomUEmpty P (n + 1) (j + 2 ^ n) = 0 := by
    have heq : atomUEmpty P (n + 1) (j + 2 ^ n) = atomUEmpty P (n + 1) k := by
      unfold atomUEmpty; rw [hpos_eq, hneg_eq]
    rw [heq]; exact hne
  apply Set.Subset.antisymm
  · have hsub1 : UX (atomUCode P (n + 1) k) ⊆ UX (atomUCode P n k) := atomUCode.subset P hne
    have hsub2 : UX (atomUCode P (n + 1) k) ⊆ UX (YseqCode P n) := by
      rw [hcode_eq]
      intro z hz
      exact (mem_UX_YseqCode_iff P n z).mpr ⟨j, hjlt, hempty_eq, hz⟩
    exact Set.subset_inter hsub1 hsub2
  · rintro z ⟨hzB, hzY⟩
    obtain ⟨i, hilt, hie, hz⟩ := (mem_UX_YseqCode_iff P n z).mp hzY
    by_cases hagree' : ∀ p < n, deltaOf (i + 2 ^ n) p = deltaOf k p
    · have hagreeFull : ∀ l < n + 1, deltaOf (i + 2 ^ n) l = deltaOf k l := by
        intro l hl
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | rfl
        · exact hagree' l hl'
        · rw [deltaOf_two_pow_add_self hilt, hδ]
      have hcode_eq'' : atomUCode P (n + 1) (i + 2 ^ n) = atomUCode P (n + 1) k :=
        (atomUCodeState_congr P hagreeFull).2.2
      rw [← hcode_eq'']; exact hz
    · push Not at hagree'
      obtain ⟨l, hl, hlne⟩ := hagree'
      have hd : UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k) = ∅ :=
        atomUCode_disjoint P n (i + 2 ^ n) k (atomUEmpty_zero_of_succ P hie)
          (atomUEmpty_zero_of_succ P hne) ⟨l, hl, hlne⟩
      have hzB' : z ∈ UX (atomUCode P n (i + 2 ^ n)) := atomUCode.subset P hie hz
      have hzmem : z ∈ UX (atomUCode P n (i + 2 ^ n)) ∩ UX (atomUCode P n k) := ⟨hzB', hzB⟩
      rw [hd] at hzmem
      exact absurd hzmem (Set.mem_empty_iff_false z).mp

theorem atomUCode_inter_succ_empty_of_junk {n k : ℕ} (hn0 : atomUEmpty P n k = 0)
    (hjunk : atomUEmpty P (n + 1) k = 1) :
    UX (atomUCode P n k) ∩ (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅ := by

  rcases Bool.eq_false_or_eq_true (deltaOf k n) with hδ | hδ
  ·
    have hjlt0 : k % 2 ^ n < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
    have hagree : ∀ l < n + 1, deltaOf (k % 2 ^ n + 2 ^ n) l = deltaOf k l := by
      intro l hl
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | rfl
      · rw [deltaOf_add_two_pow_of_lt _ hl', deltaOf_mod_two_pow_of_lt hl']
      · rw [deltaOf_two_pow_add_self hjlt0, hδ]
    obtain ⟨hp, hnge, -⟩ := atomUCodeState_congr P hagree
    have htwinJunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 1 := by
      unfold atomUEmpty
      rw [hp, hnge]
      exact hjunk
    rw [ite_eq_left hδ]
    exact atomUCode_disjoint_YseqCode_of_posTwin_empty P hn0 htwinJunk
  ·

    have hbit0 : (k / 2 ^ n) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hh | hh
      · exact hh
      · exact absurd ((deltaOf_eq_true_iff k n).mpr hh) (by simp [hδ])
    have hempJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 1 := by
      have h := hjunk
      rw [atomUEmpty_succ, hbit0, selectFn_zero] at h
      exact h
    have hJempty : DAtom (P0 P) (decodeList (atomUPos P n k))
        (n :: decodeList (atomUNeg P n k)) = ∅ := by
      have h := (datomDec_spec P (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)).mp hempJ
      rwa [decodeList_succ, unpair_pair_fst, unpair_pair_snd] at h
    have hDunion := DAtom_union P n (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k))
    have hIeqAll : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) =
        DAtom (P0 P) (n :: decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) := by
      rw [hDunion, hJempty, Set.union_empty]
    have hIeqAll' : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) =
        DAtom (P0 P) (decodeList (Nat.pair n (atomUPos P n k) + 1)) (decodeList (atomUNeg P n k)) := by
      rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd]; exact hIeqAll
    have hne0 : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) ≠ ∅ := by
      intro hcon
      have := (atomUEmpty_eq_one_iff P n k).mpr hcon
      omega
    have hemptyI0 : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 0 := by
      apply datomDec_eq_zero
      rw [← hIeqAll']
      exact hne0
    have hjlt : k % 2 ^ n < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
    obtain ⟨htwinPos, htwinNeg, htwinCode⟩ := atomUCodeState_congr_twin P n k
    have htwinBit1 : (k % 2 ^ n + 2 ^ n) / 2 ^ n % 2 = 1 := by
      have hh := deltaOf_two_pow_add_self hjlt
      rw [deltaOf_eq_true_iff] at hh
      exact hh
    have htwinNonjunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 0 := by
      rw [atomUEmpty_succ, htwinBit1, selectFn_one, htwinPos, htwinNeg]
      exact hemptyI0
    have hδtwin : deltaOf (k % 2 ^ n + 2 ^ n) n = true := deltaOf_two_pow_add_self hjlt
    have hkey := atomUCode_succ_true P htwinNonjunk hδtwin
    have htwinCodeVal : atomUCode P (n + 1) (k % 2 ^ n + 2 ^ n) = atomUCode P n k := by
      rw [atomUCode.succ, htwinBit1, selectFn_one, htwinPos, htwinNeg, hemptyI0, selectFn_zero,
        htwinCode, hempJ, selectFn_one]
    rw [htwinCodeVal, htwinCode] at hkey
    have hsub : UX (atomUCode P n k) ⊆ Yc P n := by
      intro z hz
      have hz' : z ∈ UX (atomUCode P n k) ∩ UX (YseqCode P n) := by rw [← hkey]; exact hz
      exact hz'.2
    rw [ite_eq_right (by simp [hδ])]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz1, -, hz2⟩
    exact hz2 (hsub hz1)

theorem atomUCode_succ_false {k n : ℕ} (hne : atomUEmpty P (n + 1) k = 0)
    (hδ : deltaOf k n = false) :
    UX (atomUCode P (n + 1) k) = UX (atomUCode P n k) \ UX (YseqCode P n) := by
  have hjlt : k % 2 ^ n < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
  obtain ⟨htwinPos, htwinNeg, htwinCode⟩ := atomUCodeState_congr_twin P n k
  have hbit0 : (k / 2 ^ n) % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hh | hh
    · exact hh
    · exact absurd ((deltaOf_eq_true_iff k n).mpr hh) (by simp [hδ])
  have hempJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 0 := by
    have h := hne
    rw [atomUEmpty_succ, hbit0, selectFn_zero] at h
    exact h
  have hncode : atomUCode P (n + 1) k = selectFn
      (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)))
      (atomUCode P n k) (splitURight (atomUCode P n k)) := by
    rw [atomUCode.succ, hbit0, selectFn_zero, hempJ, selectFn_zero]
  have htwinBit1 : (k % 2 ^ n + 2 ^ n) / 2 ^ n % 2 = 1 := by
    have hh := deltaOf_two_pow_add_self hjlt
    rw [deltaOf_eq_true_iff] at hh
    exact hh
  have htwinEmpty : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) =
      datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) := by
    rw [atomUEmpty_succ, htwinBit1, selectFn_one, htwinPos, htwinNeg]
  have hIle := datomDec_le_one P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k))
  rcases (by omega :
      datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 0 ∨
      datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 1) with hI | hI
  ·
    have htwinCodeVal : atomUCode P (n + 1) (k % 2 ^ n + 2 ^ n) = splitULeft (atomUCode P n k) := by
      rw [atomUCode.succ, htwinBit1, selectFn_one, htwinPos, htwinNeg, htwinCode, hI, selectFn_zero,
        hempJ, selectFn_zero]
    have htwinNonjunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 0 := by rw [htwinEmpty, hI]
    have hδtwin : deltaOf (k % 2 ^ n + 2 ^ n) n = true := deltaOf_two_pow_add_self hjlt
    have hkey := atomUCode_succ_true P htwinNonjunk hδtwin
    rw [htwinCodeVal, htwinCode] at hkey
    have hunion := splitU_union (atomUCode P n k)
    have hdisj := splitU_disjoint (atomUCode P n k)
    have hUXeq : UX (splitURight (atomUCode P n k)) =
        UX (atomUCode P n k) \ UX (splitULeft (atomUCode P n k)) := by
      apply Set.Subset.antisymm
      · intro z hz
        refine ⟨?_, fun hzL => ?_⟩
        · rw [← hunion]; exact Set.mem_union_right _ hz
        · have hz' : z ∈ UX (splitULeft (atomUCode P n k)) ∩ UX (splitURight (atomUCode P n k)) :=
            ⟨hzL, hz⟩
          rw [hdisj] at hz'
          exact hz'
      · rintro z ⟨hzC, hznL⟩
        rw [← hunion] at hzC
        exact hzC.resolve_left hznL
    rw [hncode, hI, selectFn_zero, hUXeq, hkey]
    apply Set.Subset.antisymm
    · rintro z ⟨hzC, hznCY⟩
      exact ⟨hzC, fun hzY => hznCY ⟨hzC, hzY⟩⟩
    · rintro z ⟨hzC, hznY⟩
      exact ⟨hzC, fun hzY => hznY hzY.2⟩
  ·
    have htwinNonjunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 1 := by rw [htwinEmpty, hI]
    have hk : atomUEmpty P n k = 0 := atomUEmpty_zero_of_succ P hne
    have hcdisj : UX (atomUCode P n k) ∩ UX (YseqCode P n) = ∅ :=
      atomUCode_disjoint_YseqCode_of_posTwin_empty P hk htwinNonjunk
    have hEq : UX (atomUCode P n k) = UX (atomUCode P n k) \ UX (YseqCode P n) := by
      apply Set.Subset.antisymm
      · intro z hz
        refine ⟨hz, fun hzY => ?_⟩
        have hz' : z ∈ UX (atomUCode P n k) ∩ UX (YseqCode P n) := ⟨hz, hzY⟩
        rw [hcdisj] at hz'
        exact hz'
      · exact Set.sdiff_subset
    rw [hncode, hI, selectFn_one]
    exact hEq

theorem atomUCode_eq_genAtomYseqCode (k : ℕ) :
    ∀ n, atomUEmpty P n k = 0 → UX (atomUCode P n k) = genAtom (Yc P) U.master (deltaOf k) n := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [atomUCode.zero, UX_UmasterIdx]
    rfl
  | succ n ih =>
    intro hne
    have ihn := ih (atomUEmpty_zero_of_succ P hne)

    rcases Bool.eq_false_or_eq_true (deltaOf k n) with hδ | hδ
    · have hstep : genAtom (Yc P) U.master (deltaOf k) (n + 1) =
          genAtom (Yc P) U.master (deltaOf k) n ∩ Yc P n := by
        show genAtom (Yc P) U.master (deltaOf k) n ∩
          (if deltaOf k n then Yc P n else U.master \ Yc P n) = _
        simp [hδ]
      rw [hstep, ← ihn, atomUCode_succ_true P hne hδ]
      rfl
    · have hstep : genAtom (Yc P) U.master (deltaOf k) (n + 1) =
          genAtom (Yc P) U.master (deltaOf k) n ∩ (U.master \ Yc P n) := by
        show genAtom (Yc P) U.master (deltaOf k) n ∩
          (if deltaOf k n then Yc P n else U.master \ Yc P n) = _
        simp [hδ]
      rw [hstep, ← ihn, atomUCode_succ_false P hne hδ]
      have hsub : UX (atomUCode P n k) ⊆ U.master := by
        rw [ihn]; exact genAtom_subset (Yc P) U.master (deltaOf k) n
      apply Set.Subset.antisymm
      · intro z hz; exact ⟨hz.1, hsub hz.1, hz.2⟩
      · rintro z ⟨hz1, -, hz2⟩; exact ⟨hz1, hz2⟩

theorem genAtom_Yc_empty_iff (n k : ℕ) :
    genAtom (Yc P) U.master (deltaOf k) n = ∅ ↔ atomUEmpty P n k = 1 := by
  induction n with
  | zero =>
    have h0 : atomUEmpty P 0 k = 0 := by
      have hne : genAtom (idxSet (e P)) Set.univ (deltaOf k) 0 ≠ ∅ := by
        show (Set.univ : Set ℕ) ≠ ∅
        exact Set.univ_nonempty.ne_empty
      exact (atomUEmpty_eq_zero_iff_genAtom P 0 k).mpr hne
    constructor
    · intro h
      exact absurd h (Set.Nonempty.ne_empty U.master_mem.2.1)
    · intro h; omega
  | succ n ih =>
    have hle : atomUEmpty P (n + 1) k ≤ 1 := datomDec_le_one P _
    rcases (by omega : atomUEmpty P (n + 1) k = 0 ∨ atomUEmpty P (n + 1) k = 1) with h1 | h1
    · have heq' := atomUCode_eq_genAtomYseqCode P k (n + 1) h1
      constructor
      · intro hempty
        rw [← heq'] at hempty
        exact absurd hempty (U_mem_UX _).2.1.ne_empty
      · intro hcontra; omega
    · by_cases hn0 : atomUEmpty P n k = 0
      · have heq := atomUCode_eq_genAtomYseqCode P k n hn0
        have hempty : genAtom (Yc P) U.master (deltaOf k) (n + 1) = ∅ := by
          show genAtom (Yc P) U.master (deltaOf k) n ∩
            (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅
          rw [← heq]
          exact atomUCode_inter_succ_empty_of_junk P hn0 h1
        exact ⟨fun _ => h1, fun _ => hempty⟩
      · push Not at hn0
        have hle0 : atomUEmpty P n k ≤ 1 := datomDec_le_one P _
        have hn1 : atomUEmpty P n k = 1 := by omega
        have hprev : genAtom (Yc P) U.master (deltaOf k) n = ∅ := ih.mpr hn1
        have hempty : genAtom (Yc P) U.master (deltaOf k) (n + 1) = ∅ := by
          show genAtom (Yc P) U.master (deltaOf k) n ∩
            (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅
          rw [hprev, Set.empty_inter]
        exact ⟨fun _ => h1, fun _ => hempty⟩

end

end DomainTheory.NeighbourhoodSystems
