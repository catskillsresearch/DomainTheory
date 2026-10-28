module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UX
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.QPairCodes

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open Domain.Recursive NeighborhoodSystem

open Domain.Recursive NeighborhoodSystem

def clipGeCode (t : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1)) t.unpair.2.unpair.2

def clipGeListCode (m c : ℕ) : ℕ := flatMapCode (fun t => Nat.pair (clipGeCode t) 0 + 1) m c

def clipLtCode (t : ℕ) : ℕ :=
  Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1))

def clipLtListCode (m c : ℕ) : ℕ := flatMapCode (fun t => Nat.pair (clipLtCode t) 0 + 1) m c

def firstElemCode (c : ℕ) : ℕ := (c - 1).unpair.1

def qpClipGe (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1 ⊔ m, p.2)

def qpClipLt (m : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1, p.2 ⊓ m)

def splitMidCode (n : ℕ) : ℕ := ratMidCode (firstElemCode (canonCode n))

def splitULeft (n : ℕ) : ℕ := clipLtListCode (splitMidCode n) (canonCode n)

def splitURight (n : ℕ) : ℕ := clipGeListCode (splitMidCode n) (canonCode n)

theorem decodeQPairList_singletonCode (v : ℕ) :
    decodeQPairList (Nat.pair v 0 + 1) = [decodeRatPair v] := by
  unfold decodeQPairList
  rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
  rfl

theorem decodeRatPair_clipGeCode (m e : ℕ) :
    decodeRatPair (clipGeCode (Nat.pair m e)) = qpClipGe (decodeRat m) (decodeRatPair e) := by
  unfold clipGeCode decodeRatPair qpClipGe
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_ratMaxCode]

theorem decodeRatPair_clipLtCode (m e : ℕ) :
    decodeRatPair (clipLtCode (Nat.pair m e)) = qpClipLt (decodeRat m) (decodeRatPair e) := by
  unfold clipLtCode decodeRatPair qpClipLt
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_ratMinCode]

theorem mem_decodeQPairList_clipGeListCode (m c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (clipGeListCode m c) ↔
      ∃ p0 ∈ decodeQPairList c, p = qpClipGe (decodeRat m) p0 := by
  unfold clipGeListCode
  rw [mem_decodeQPairList_flatMapCode]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipGeCode] at hp
    exact ⟨decodeRatPair y, (mem_decodeQPairList c (decodeRatPair y)).mpr ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p0, hp0, hp⟩
    obtain ⟨y, hy, rfl⟩ := (mem_decodeQPairList c p0).mp hp0
    exact ⟨y, hy, by
      rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipGeCode]; exact hp⟩

theorem mem_decodeQPairList_clipLtListCode (m c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (clipLtListCode m c) ↔
      ∃ p0 ∈ decodeQPairList c, p = qpClipLt (decodeRat m) p0 := by
  unfold clipLtListCode
  rw [mem_decodeQPairList_flatMapCode]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipLtCode] at hp
    exact ⟨decodeRatPair y, (mem_decodeQPairList c (decodeRatPair y)).mpr ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p0, hp0, hp⟩
    obtain ⟨y, hy, rfl⟩ := (mem_decodeQPairList c p0).mp hp0
    exact ⟨y, hy, by
      rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipLtCode]; exact hp⟩

theorem mem_decodeQPairList_firstElemCode {c : ℕ} (hc : c ≠ 0) :
    decodeRatPair (firstElemCode c) ∈ decodeQPairList c := by
  obtain ⟨c', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc
  have : firstElemCode (c' + 1) = c'.unpair.1 := by unfold firstElemCode; simp
  unfold decodeQPairList
  rw [this, decodeList_succ]
  exact List.mem_map_of_mem (by simp)

theorem presentedIntervals_map_qpClipGe (m : ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map (qpClipGe m)) = presentedIntervals L ∩ Set.Ici m := by
  ext x
  simp only [presentedIntervals.mem, List.mem_map, Set.mem_inter_iff, Set.mem_Ici, qpClipGe]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, le_sup_left.trans hx1, hx2⟩, le_sup_right.trans hx1⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hxm⟩
    exact ⟨(q.1 ⊔ m, q.2), ⟨q, hq, rfl⟩, sup_le hxq1 hxm, hxq2⟩

theorem presentedIntervals_decodeQPairList_clipGeListCode (m c : ℕ) :
    presentedIntervals (decodeQPairList (clipGeListCode m c)) =
      presentedIntervals (decodeQPairList c) ∩ Set.Ici (decodeRat m) := by
  rw [← presentedIntervals_map_qpClipGe]
  apply presentedIntervals.congr
  intro p
  rw [mem_decodeQPairList_clipGeListCode, List.mem_map]
  simp only [eq_comm]

theorem presentedIntervals_map_qpClipLt (m : ℚ) (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map (qpClipLt m)) = presentedIntervals L ∩ Set.Iio m := by
  ext x
  simp only [presentedIntervals.mem, List.mem_map, Set.mem_inter_iff, Set.mem_Iio, qpClipLt]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, hx1, hx2.trans_le inf_le_left⟩, hx2.trans_le inf_le_right⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hxm⟩
    exact ⟨(q.1, q.2 ⊓ m), ⟨q, hq, rfl⟩, hxq1, lt_inf_iff.mpr ⟨hxq2, hxm⟩⟩

theorem presentedIntervals_decodeQPairList_clipLtListCode (m c : ℕ) :
    presentedIntervals (decodeQPairList (clipLtListCode m c)) =
      presentedIntervals (decodeQPairList c) ∩ Set.Iio (decodeRat m) := by
  rw [← presentedIntervals_map_qpClipLt]
  apply presentedIntervals.congr
  intro p
  rw [mem_decodeQPairList_clipLtListCode, List.mem_map]
  simp only [eq_comm]

theorem primrec_clipGeCode : Nat.Primrec clipGeCode := by
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have he1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have he2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.pair (primrec_ratMaxCode.comp (he1.pair hm)) he2).of_eq
    fun t => by simp only [clipGeCode]

theorem primrec_clipGeListCode : Nat.Primrec (fun t : ℕ => clipGeListCode t.unpair.1 t.unpair.2) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (clipGeCode t) 0 + 1) :=
    Nat.Primrec.succ.comp (primrec_clipGeCode.pair (Nat.Primrec.const 0))
  exact (primrec_flatMapCode hg).of_eq fun _ => rfl

theorem primrec_clipLtCode : Nat.Primrec clipLtCode := by
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have he1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have he2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.pair he1 (primrec_ratMinCode.comp (he2.pair hm))).of_eq
    fun t => by simp only [clipLtCode]

theorem primrec_clipLtListCode : Nat.Primrec (fun t : ℕ => clipLtListCode t.unpair.1 t.unpair.2) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (clipLtCode t) 0 + 1) :=
    Nat.Primrec.succ.comp (primrec_clipLtCode.pair (Nat.Primrec.const 0))
  exact (primrec_flatMapCode hg).of_eq fun _ => rfl

theorem primrec_firstElemCode : Nat.Primrec firstElemCode :=
  Nat.Primrec.left.comp primrec_pred

theorem primrec_splitMidCode : Nat.Primrec splitMidCode :=
  (primrec_ratMidCode.comp (primrec_firstElemCode.comp primrec_canonCode)).of_eq fun n => by
    simp only [splitMidCode]

theorem primrec_splitULeft : Nat.Primrec splitULeft :=
  (primrec_clipLtListCode.comp (primrec_splitMidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [splitULeft, unpair_pair_fst, unpair_pair_snd]

theorem primrec_splitURight : Nat.Primrec splitURight :=
  (primrec_clipGeListCode.comp (primrec_splitMidCode.pair primrec_canonCode)).of_eq
    fun n => by simp only [splitURight, unpair_pair_fst, unpair_pair_snd]

theorem splitU_p0_lt (n : ℕ) :
    (decodeRatPair (firstElemCode (canonCode n))).1 < (decodeRatPair (firstElemCode (canonCode n))).2 :=
  forall_lt_decodeQPairList_canonCode n _
    (mem_decodeQPairList_firstElemCode (canonCode_ne_zero n))

theorem splitU_mid_gt (n : ℕ) :
    (decodeRatPair (firstElemCode (canonCode n))).1 < decodeRat (splitMidCode n) := by
  show decodeRat (firstElemCode (canonCode n)).unpair.1 < decodeRat (splitMidCode n)
  unfold splitMidCode
  rw [decodeRat_ratMidCode']
  have h := splitU_p0_lt n
  unfold decodeRatPair at h
  exact left_lt_add_div_two.mpr h

theorem UX_splitULeft (n : ℕ) :
    UX (splitULeft n) = UX n ∩ Set.Iio (decodeRat (splitMidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitULeft n))) := by
    show U.mem (presentedIntervals (decodeQPairList (clipLtListCode (splitMidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipLtListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipLt (decodeRat (splitMidCode n))),
      (presentedIntervals_map_qpClipLt _ _).symm⟩, ?_, ?_⟩
    · refine ⟨(decodeRatPair (firstElemCode (canonCode n))).1, ?_, splitU_mid_gt n⟩
      exact presentedIntervals.mem.mpr ⟨decodeRatPair (firstElemCode (canonCode n)),
        mem_decodeQPairList_firstElemCode (canonCode_ne_zero n), le_refl _, splitU_p0_lt n⟩
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitULeft n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipLtListCode (splitMidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipLtListCode]
  rfl

theorem splitU_mid_lt (n : ℕ) :
    decodeRat (splitMidCode n) < (decodeRatPair (firstElemCode (canonCode n))).2 := by
  show decodeRat (splitMidCode n) < decodeRat (firstElemCode (canonCode n)).unpair.2
  unfold splitMidCode
  rw [decodeRat_ratMidCode']
  have h := splitU_p0_lt n
  unfold decodeRatPair at h
  exact add_div_two_lt_right.mpr h

theorem UX_splitURight (n : ℕ) :
    UX (splitURight n) = UX n ∩ Set.Ici (decodeRat (splitMidCode n)) := by
  have hUL : U.mem (presentedIntervals (decodeQPairList (splitURight n))) := by
    show U.mem (presentedIntervals (decodeQPairList (clipGeListCode (splitMidCode n) (canonCode n))))
    rw [presentedIntervals_decodeQPairList_clipGeListCode]
    refine ⟨⟨(decodeQPairList (canonCode n)).map (qpClipGe (decodeRat (splitMidCode n))),
      (presentedIntervals_map_qpClipGe _ _).symm⟩, ?_, ?_⟩
    · refine ⟨decodeRat (splitMidCode n), ?_, Set.self_mem_Ici⟩
      exact presentedIntervals.mem.mpr ⟨decodeRatPair (firstElemCode (canonCode n)),
        mem_decodeQPairList_firstElemCode (canonCode_ne_zero n), (splitU_mid_gt n).le, splitU_mid_lt n⟩
    · exact Set.inter_subset_left.trans (U_mem_UX n).2.2
  show presentedIntervals (decodeQPairList (canonCode (splitURight n))) = _
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL]
  show presentedIntervals (decodeQPairList (clipGeListCode (splitMidCode n) (canonCode n))) = _
  rw [presentedIntervals_decodeQPairList_clipGeListCode]
  rfl

theorem splitU_disjoint (n : ℕ) : UX (splitULeft n) ∩ UX (splitURight n) = ∅ := by
  rw [UX_splitULeft, UX_splitURight]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨-, h1⟩, -, h2⟩
  exact absurd h1 (not_lt.mpr h2)

theorem splitU_left_ne (n : ℕ) : UX (splitULeft n) ≠ UX n := by
  intro hEq
  have hZsub : UX (splitURight n) ⊆ UX (splitULeft n) := by
    rw [hEq, UX_splitURight]; exact Set.inter_subset_left
  have hZempty : UX (splitURight n) ⊆ (∅ : Set ℚ) := by
    rw [← splitU_disjoint n]; exact Set.subset_inter hZsub subset_rfl
  exact (U_mem_UX (splitURight n)).2.1.ne_empty (Set.subset_empty_iff.mp hZempty)

theorem splitU_right_ne (n : ℕ) : UX (splitURight n) ≠ UX n := by
  intro hEq
  have hYsub : UX (splitULeft n) ⊆ UX (splitURight n) := by
    rw [hEq, UX_splitULeft]; exact Set.inter_subset_left
  have hYempty : UX (splitULeft n) ⊆ (∅ : Set ℚ) := by
    rw [← splitU_disjoint n]; exact Set.subset_inter subset_rfl hYsub
  exact (U_mem_UX (splitULeft n)).2.1.ne_empty (Set.subset_empty_iff.mp hYempty)

theorem splitU_union (n : ℕ) : UX (splitULeft n) ∪ UX (splitURight n) = UX n := by
  rw [UX_splitULeft, UX_splitURight]
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    rcases lt_or_ge x (decodeRat (splitMidCode n)) with hlt | hge
    · exact Or.inl ⟨h, hlt⟩
    · exact Or.inr ⟨h, hge⟩

end DomainTheory.NeighbourhoodSystems
