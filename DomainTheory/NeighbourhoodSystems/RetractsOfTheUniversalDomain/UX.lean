module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.QPairCodes
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.presentedIntervals
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open Domain.Recursive NeighborhoodSystem

def masterPairCode : ℕ := Nat.pair zeroCode oneCode

@[simp] theorem decodeRatPair_masterPairCode : decodeRatPair masterPairCode = ((0 : ℚ), (1 : ℚ)) := by
  unfold masterPairCode decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_zeroCode, decodeRat_oneCode]

def UmasterIdx : ℕ := encodeQPairList [((0 : ℚ), (1 : ℚ))]

theorem decodeQPairList_masterCode :
    decodeQPairList (Nat.pair masterPairCode 0 + 1) = [((0 : ℚ), (1 : ℚ))] := by
  unfold decodeQPairList
  rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
  simp [decodeRatPair_masterPairCode]

theorem presentedIntervals_eq_empty_iff_of_forall_lt {L' : List (ℚ × ℚ)}
    (hpos : ∀ p ∈ L', p.1 < p.2) : presentedIntervals L' = ∅ ↔ L' = [] := by
  constructor
  · intro h
    rcases L' with _ | ⟨a, l⟩
    · rfl
    · exact absurd h (Set.Nonempty.ne_empty ⟨a.1, presentedIntervals.mem.mpr
        ⟨a, List.mem_cons.mpr (Or.inl rfl), le_refl _,
          hpos a (List.mem_cons.mpr (Or.inl rfl))⟩⟩)
  · rintro rfl; exact presentedIntervals.nil

theorem presentedIntervals_filter_qpPos (L : List (ℚ × ℚ)) :
    presentedIntervals (L.filter (fun p => decide (p.1 < p.2))) = presentedIntervals L := by
  ext x
  simp only [presentedIntervals.mem, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨hp, -⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx1, hx2⟩
    exact ⟨p, ⟨hp, lt_of_le_of_lt hx1 hx2⟩, hx1, hx2⟩

theorem presentedIntervals_singleton_zero_one :
    presentedIntervals ([((0 : ℚ), (1 : ℚ))]) = U.master := by
  rw [presentedIntervals.cons, presentedIntervals.nil, Set.union_empty]; rfl

def qpClip (p : ℚ × ℚ) : ℚ × ℚ := (p.1 ⊔ 0, p.2 ⊓ 1)

def canonList (L : List (ℚ × ℚ)) : List (ℚ × ℚ) :=
  match (L.map qpClip).filter (fun p => decide (p.1 < p.2)) with
  | [] => [((0 : ℚ), (1 : ℚ))]
  | L' => L'

theorem canonList_eq_of_filter_eq_cons {L : List (ℚ × ℚ)} {a : ℚ × ℚ} {l : List (ℚ × ℚ)}
    (h : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) = a :: l) :
    canonList L = a :: l := by
  unfold canonList; rw [h]

theorem canonList_eq_of_filter_eq_nil {L : List (ℚ × ℚ)}
    (h : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) = []) :
    canonList L = [((0 : ℚ), (1 : ℚ))] := by
  unfold canonList; rw [h]

theorem presentedIntervals_map_qpClip (L : List (ℚ × ℚ)) :
    presentedIntervals (L.map qpClip) = presentedIntervals L ∩ Set.Ico (0 : ℚ) 1 := by
  ext x
  simp only [presentedIntervals.mem, List.mem_map, Set.mem_inter_iff, Set.mem_Ico, qpClip]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hx1, hx2⟩
    exact ⟨⟨q, hq, le_sup_left.trans hx1, hx2.trans_le inf_le_left⟩,
      le_sup_right.trans hx1, hx2.trans_le inf_le_right⟩
  · rintro ⟨⟨q, hq, hxq1, hxq2⟩, hx0, hx1⟩
    exact ⟨(q.1 ⊔ 0, q.2 ⊓ 1), ⟨q, hq, rfl⟩, sup_le hxq1 hx0, lt_inf_iff.mpr ⟨hxq2, hx1⟩⟩

theorem U_presentedIntervals.mem_canonList (L : List (ℚ × ℚ)) :
    U.mem (presentedIntervals (canonList L)) := by
  rcases hL : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
  · rw [canonList_eq_of_filter_eq_nil hL]
    have heq : presentedIntervals ([((0 : ℚ), (1 : ℚ))]) = U.master := by
      rw [presentedIntervals.cons, presentedIntervals.nil, Set.union_empty]; rfl
    rw [heq]; exact U.master_mem
  · rw [canonList_eq_of_filter_eq_cons hL]
    have hL'eq : presentedIntervals (a :: l) = presentedIntervals L ∩ Set.Ico (0 : ℚ) 1 := by
      rw [← hL, presentedIntervals_filter_qpPos, presentedIntervals_map_qpClip]
    have hmem : a ∈ (L.map qpClip).filter (fun p => decide (p.1 < p.2)) := by
      rw [hL]; exact List.mem_cons.mpr (Or.inl rfl)
    have ha : a.1 < a.2 := by simpa using (List.mem_filter.mp hmem).2
    refine ⟨⟨a :: l, rfl⟩, ?_, hL'eq ▸ Set.inter_subset_right⟩
    exact ⟨a.1, presentedIntervals.mem.mpr ⟨a, List.mem_cons.mpr (Or.inl rfl), le_refl _, ha⟩⟩

theorem canonList_fixed {L : List (ℚ × ℚ)} (h : U.mem (presentedIntervals L)) :
    presentedIntervals (canonList L) = presentedIntervals L := by
  obtain ⟨-, hne, hsub⟩ := h
  rcases hL : (L.map qpClip).filter (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
  · exfalso
    have hcontra : presentedIntervals L ∩ Set.Ico (0 : ℚ) 1 = ∅ := by
      rw [← presentedIntervals_map_qpClip, ← presentedIntervals_filter_qpPos (L.map qpClip), hL,
        presentedIntervals.nil]
    rw [Set.inter_eq_left.mpr hsub] at hcontra
    exact hne.ne_empty hcontra
  · rw [canonList_eq_of_filter_eq_cons hL, ← hL, presentedIntervals_filter_qpPos,
      presentedIntervals_map_qpClip, Set.inter_eq_left.mpr hsub]

def qpClipCode (e : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair e.unpair.1 zeroCode)) (ratMinCode (Nat.pair e.unpair.2 oneCode))

def canonFilterStep (e : ℕ) : ℕ :=
  selectFn (qpNonemptyBop (qpClipCode e)) (Nat.pair (qpClipCode e) 0 + 1) 0

def canonListCode (c : ℕ) : ℕ := flatMapCode (fun t => canonFilterStep t.unpair.2) 0 c

def canonCode (c : ℕ) : ℕ :=
  selectFn (isZero (canonListCode c)) (Nat.pair masterPairCode 0 + 1) (canonListCode c)

def UX (n : ℕ) : Set ℚ := presentedIntervals (decodeQPairList (canonCode n))

def Uinter (n m : ℕ) : ℕ := combineCode (canonCode n) (canonCode m)

theorem decodeRatPair_qpClipCode (e : ℕ) :
    decodeRatPair (qpClipCode e) = qpClip (decodeRatPair e) := by
  unfold qpClipCode qpClip decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [decodeRat_ratMaxCode, decodeRat_ratMinCode, decodeRat_zeroCode, decodeRat_oneCode]

theorem decodeList_canonFilterStep (e : ℕ) :
    decodeList (canonFilterStep e)
      = if (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2
        then [qpClipCode e] else [] := by
  unfold canonFilterStep
  by_cases h : qpNonemptyBop (qpClipCode e) = 1
  · rw [h, selectFn_one]
    have h' : (decodeRatPair (qpClipCode e)).1 < (decodeRatPair (qpClipCode e)).2 :=
      (qpNonemptyBop_eq_one_iff (qpClipCode e)).mp h
    rw [decodeRatPair_qpClipCode] at h'
    simp [h', decodeList_succ, decodeList_zero]
  · have h0 : qpNonemptyBop (qpClipCode e) = 0 := by
      have := ratLtCode_le_one (Nat.pair (qpClipCode e).unpair.1 (qpClipCode e).unpair.2)
      unfold qpNonemptyBop at h ⊢; omega
    rw [h0, selectFn_zero]
    have hnot : ¬ (decodeRatPair (qpClipCode e)).1 < (decodeRatPair (qpClipCode e)).2 := by
      rw [← qpNonemptyBop_eq_one_iff]; omega
    rw [decodeRatPair_qpClipCode] at hnot
    simp [hnot, decodeList_zero]

theorem decodeQPairList_canonFilterStep (e : ℕ) :
    decodeQPairList (canonFilterStep e)
      = if (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2
        then [qpClip (decodeRatPair e)] else [] := by
  unfold decodeQPairList
  rw [decodeList_canonFilterStep]
  split <;> simp [decodeRatPair_qpClipCode]

theorem mem_decodeQPairList_canonFilterStep (e : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (canonFilterStep e) ↔
      (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2 ∧ p = qpClip (decodeRatPair e) := by
  rw [decodeQPairList_canonFilterStep]
  by_cases h : (qpClip (decodeRatPair e)).1 < (qpClip (decodeRatPair e)).2
  · simp [h]
  · simp [h]

theorem mem_decodeQPairList_canonListCode (c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (canonListCode c) ↔
      ∃ p0 ∈ decodeQPairList c, (qpClip p0).1 < (qpClip p0).2 ∧ p = qpClip p0 := by
  unfold canonListCode
  rw [mem_decodeQPairList_flatMapCode]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [unpair_pair_snd, mem_decodeQPairList_canonFilterStep] at hp
    exact ⟨decodeRatPair y, (mem_decodeQPairList c (decodeRatPair y)).mpr ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p0, hp0, hcond, hp⟩
    obtain ⟨y, hy, rfl⟩ := (mem_decodeQPairList c p0).mp hp0
    exact ⟨y, hy, by rw [unpair_pair_snd, mem_decodeQPairList_canonFilterStep]; exact ⟨hcond, hp⟩⟩

theorem decodeQPairList_canonListCode_eq_nil_iff (c : ℕ) :
    decodeQPairList (canonListCode c) = [] ↔
      presentedIntervals (decodeQPairList (canonListCode c)) = ∅ :=
  (presentedIntervals_eq_empty_iff_of_forall_lt (fun p hp => by
    obtain ⟨p0, hp0, hcond, rfl⟩ := (mem_decodeQPairList_canonListCode c p).mp hp
    exact hcond)).symm

theorem presentedIntervals_decodeQPairList_canonListCode (c : ℕ) :
    presentedIntervals (decodeQPairList (canonListCode c))
      = presentedIntervals (decodeQPairList c) ∩ Set.Ico (0 : ℚ) 1 := by
  rw [← presentedIntervals_map_qpClip, ← presentedIntervals_filter_qpPos ((decodeQPairList c).map qpClip)]
  apply presentedIntervals.congr
  intro p
  rw [mem_decodeQPairList_canonListCode, List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨p0, hp0, hcond, rfl⟩
    exact ⟨⟨p0, hp0, rfl⟩, decide_eq_true_eq.mpr hcond⟩
  · rintro ⟨⟨p0, hp0, hp⟩, hcond⟩
    rw [decide_eq_true_eq] at hcond
    exact ⟨p0, hp0, hp ▸ hcond, hp.symm⟩

theorem presentedIntervals_decodeQPairList_canonCode (c : ℕ) :
    presentedIntervals (decodeQPairList (canonCode c))
      = presentedIntervals (canonList (decodeQPairList c)) := by
  have hfilterPos : ∀ p ∈ ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)),
      p.1 < p.2 := fun p hp => by simpa using (List.mem_filter.mp hp).2
  by_cases hne : (presentedIntervals (decodeQPairList c) ∩ Set.Ico (0 : ℚ) 1).Nonempty
  · have hnc : (presentedIntervals (decodeQPairList (canonListCode c))).Nonempty := by
      rwa [presentedIntervals_decodeQPairList_canonListCode]
    have hcne : canonListCode c ≠ 0 := by
      intro h
      apply hnc.ne_empty
      unfold decodeQPairList
      rw [h, decodeList_zero, List.map_nil]
      exact presentedIntervals.nil
    have hzero : isZero (canonListCode c) = 0 := by
      by_contra hz
      have h1 := isZero_le_one (canonListCode c)
      exact hcne ((isZero_eq_one_iff _).mp (by omega))
    have hcc : canonCode c = canonListCode c := by unfold canonCode; rw [hzero, selectFn_zero]
    have hL'ne : ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)) ≠ [] := by
      rw [Ne, ← presentedIntervals_eq_empty_iff_of_forall_lt hfilterPos,
        presentedIntervals_filter_qpPos, presentedIntervals_map_qpClip]
      exact hne.ne_empty
    rcases hL : ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
    · exact absurd hL hL'ne
    · rw [hcc, presentedIntervals_decodeQPairList_canonListCode, canonList_eq_of_filter_eq_cons hL,
        ← hL, presentedIntervals_filter_qpPos, presentedIntervals_map_qpClip]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hLnil : decodeQPairList (canonListCode c) = [] := by
      rw [decodeQPairList_canonListCode_eq_nil_iff, presentedIntervals_decodeQPairList_canonListCode,
        hne]
    have hczero : canonListCode c = 0 := by
      have h' := hLnil
      unfold decodeQPairList at h'
      rwa [List.map_eq_nil_iff, decodeList_eq_nil_iff] at h'
    have hzero : isZero (canonListCode c) = 1 := by rw [hczero]; exact (isZero_eq_one_iff 0).mpr rfl
    have hcc : canonCode c = Nat.pair masterPairCode 0 + 1 := by
      unfold canonCode; rw [hzero, selectFn_one]
    have hLnil' : ((decodeQPairList c).map qpClip).filter (fun p => decide (p.1 < p.2)) = [] := by
      rw [← presentedIntervals_eq_empty_iff_of_forall_lt hfilterPos, presentedIntervals_filter_qpPos,
        presentedIntervals_map_qpClip]
      exact hne
    rw [hcc, decodeQPairList_masterCode, canonList_eq_of_filter_eq_nil hLnil']

theorem UX_eq (n : ℕ) : UX n = presentedIntervals (canonList (decodeQPairList n)) :=
  presentedIntervals_decodeQPairList_canonCode n

theorem UX_UmasterIdx : UX UmasterIdx = U.master := by
  unfold UmasterIdx
  rw [UX_eq, decodeQPairList_encodeQPairList]
  have hmem : U.mem (presentedIntervals [((0 : ℚ), (1 : ℚ))]) := by
    rw [presentedIntervals_singleton_zero_one]; exact U.master_mem
  rw [canonList_fixed hmem, presentedIntervals_singleton_zero_one]

theorem U_mem_UX (n : ℕ) : U.mem (UX n) := by
  rw [UX_eq]; exact U_presentedIntervals.mem_canonList _

theorem U_surj_UX : ∀ {Y : Set ℚ}, U.mem Y → ∃ n, UX n = Y := by
  intro Y hY
  obtain ⟨L, -, hYeq, -⟩ := U.mem_iff_scott.mp hY
  have hUL : U.mem (presentedIntervals L) := by rw [← hYeq]; exact hY
  exact ⟨encodeQPairList L, by
    rw [UX_eq, decodeQPairList_encodeQPairList, canonList_fixed hUL, ← hYeq]⟩

theorem U_cons_iff_nonempty_inter (n m : ℕ) :
    (∃ k, UX k ⊆ UX n ∩ UX m) ↔ (UX n ∩ UX m).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    exact (U_mem_UX k).2.1.mono hk
  · intro hne
    have hUmem : U.mem (UX n ∩ UX m) := by
      obtain ⟨-, -, hsubn⟩ := U_mem_UX n
      exact ⟨⟨decodeQPairList (combineCode (canonCode n) (canonCode m)),
        (presentedIntervals_decodeQPairList_combineCode (canonCode n) (canonCode m)).symm⟩,
        hne, Set.inter_subset_left.trans hsubn⟩
    obtain ⟨k, hk⟩ := U_surj_UX hUmem
    exact ⟨k, by rw [hk]⟩

theorem Uinter_spec {n m : ℕ} (h : ∃ k, UX k ⊆ UX n ∩ UX m) : UX (Uinter n m) = UX n ∩ UX m := by
  have hne : (UX n ∩ UX m).Nonempty := (U_cons_iff_nonempty_inter n m).mp h
  have hUL : U.mem (presentedIntervals (decodeQPairList (combineCode (canonCode n) (canonCode m)))) := by
    rw [presentedIntervals_decodeQPairList_combineCode]
    obtain ⟨-, -, hsubn⟩ := U_mem_UX n
    exact ⟨⟨decodeQPairList (combineCode (canonCode n) (canonCode m)),
      (presentedIntervals_decodeQPairList_combineCode (canonCode n) (canonCode m)).symm⟩,
      hne, Set.inter_subset_left.trans hsubn⟩
  unfold Uinter UX
  rw [presentedIntervals_decodeQPairList_canonCode, canonList_fixed hUL,
    presentedIntervals_decodeQPairList_combineCode]

theorem primrec_qpClipCode : Nat.Primrec qpClipCode := by
  have h1 : Nat.Primrec (fun e : ℕ => e.unpair.1) := Nat.Primrec.left
  have h2 : Nat.Primrec (fun e : ℕ => e.unpair.2) := Nat.Primrec.right
  exact ((primrec_ratMaxCode.comp (h1.pair (Nat.Primrec.const zeroCode))).pair
    (primrec_ratMinCode.comp (h2.pair (Nat.Primrec.const oneCode)))).of_eq fun _ => rfl

theorem primrec_canonFilterStep : Nat.Primrec canonFilterStep := by
  have hc : Nat.Primrec qpClipCode := primrec_qpClipCode
  exact (primrec_selectFn (primrec_qpNonemptyBop.comp hc)
    (Nat.Primrec.succ.comp (hc.pair (Nat.Primrec.const 0))) (Nat.Primrec.const 0)).of_eq
    fun _ => rfl

theorem primrec_canonListCode : Nat.Primrec canonListCode := by
  have hg : Nat.Primrec (fun t : ℕ => canonFilterStep t.unpair.2) :=
    primrec_canonFilterStep.comp Nat.Primrec.right
  exact ((primrec_flatMapCode hg).comp ((Nat.Primrec.const 0).pair primrec_id)).of_eq
    fun c => by
      unfold canonListCode
      simp only [id, unpair_pair_fst, unpair_pair_snd]

theorem primrec_canonCode : Nat.Primrec canonCode :=
  (primrec_selectFn (primrec_isZero.comp primrec_canonListCode)
    (Nat.Primrec.const (Nat.pair masterPairCode 0 + 1)) primrec_canonListCode).of_eq
    fun _ => rfl

theorem U_cons_computable : RecDecidable₂ (fun n m => ∃ k, UX k ⊆ UX n ∩ UX m) := by
  unfold RecDecidable₂
  have hcomb : Nat.Primrec (fun t : ℕ => combineCode (canonCode t.unpair.1) (canonCode t.unpair.2)) :=
    (primrec_combineCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
      (primrec_canonCode.comp Nat.Primrec.right))).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable.of_iff (fun t => ?_) (recDecidable_presentedIntervals_nonempty.comp hcomb)
  show (∃ k, UX k ⊆ UX t.unpair.1 ∩ UX t.unpair.2) ↔ _
  rw [U_cons_iff_nonempty_inter, UX, UX, presentedIntervals_decodeQPairList_combineCode]

theorem U_interEq_computable : RecDecidable₃ (fun n m k => UX n ∩ UX m = UX k) := by
  unfold RecDecidable₃
  have h1 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have h2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h3 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcomb : Nat.Primrec (fun t : ℕ =>
      combineCode (canonCode t.unpair.1) (canonCode t.unpair.2.unpair.1)) :=
    (primrec_combineCode.comp ((primrec_canonCode.comp h1).pair (primrec_canonCode.comp h2))).of_eq
      fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hg : Nat.Primrec (fun t : ℕ =>
      Nat.pair (combineCode (canonCode t.unpair.1) (canonCode t.unpair.2.unpair.1))
        (canonCode t.unpair.2.unpair.2)) := hcomb.pair (primrec_canonCode.comp h3)
  refine RecDecidable.of_iff (fun t => ?_) (recDecidable₂_presentedIntervals_eq.comp hg)
  show UX t.unpair.1 ∩ UX t.unpair.2.unpair.1 = UX t.unpair.2.unpair.2 ↔ _
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [UX, UX, UX, presentedIntervals_decodeQPairList_combineCode]

theorem Uinter_primrec : Nat.Primrec (fun t : ℕ => Uinter t.unpair.1 t.unpair.2) := by
  unfold Uinter
  exact (primrec_combineCode.comp ((primrec_canonCode.comp Nat.Primrec.left).pair
    (primrec_canonCode.comp Nat.Primrec.right))).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

def UComputablePresentation : ComputablePresentation U where
  X := UX
  mem_X := U_mem_UX
  surj := U_surj_UX
  interEq_computable := U_interEq_computable
  cons_computable := U_cons_computable
  inter := Uinter
  inter_primrec := Uinter_primrec
  inter_spec := Uinter_spec
  masterIdx := UmasterIdx
  masterIdx_spec := UX_UmasterIdx

theorem U_isEffectivelyGiven : U.IsEffectivelyGiven := ⟨UComputablePresentation⟩

theorem decodeQPairList_canonCode_ne_nil (c : ℕ) : decodeQPairList (canonCode c) ≠ [] := by
  unfold canonCode
  by_cases hz : canonListCode c = 0
  · have hzero : isZero (canonListCode c) = 1 := by rw [hz]; exact (isZero_eq_one_iff 0).mpr rfl
    rw [hzero, selectFn_one, decodeQPairList_masterCode]
    simp
  · have hzero : isZero (canonListCode c) = 0 := by
      by_contra hcontra
      have h1 := isZero_le_one (canonListCode c)
      exact hz ((isZero_eq_one_iff _).mp (by omega))
    rw [hzero, selectFn_zero]
    intro hcontra
    apply hz
    have h' := hcontra
    unfold decodeQPairList at h'
    rwa [List.map_eq_nil_iff, decodeList_eq_nil_iff] at h'

theorem canonCode_ne_zero (c : ℕ) : canonCode c ≠ 0 := by
  intro h
  exact decodeQPairList_canonCode_ne_nil c (by rw [h]; unfold decodeQPairList; rw [decodeList_zero]; rfl)

theorem forall_lt_decodeQPairList_canonListCode (c : ℕ) :
    ∀ p ∈ decodeQPairList (canonListCode c), p.1 < p.2 := fun p hp => by
  obtain ⟨p0, -, hcond, rfl⟩ := (mem_decodeQPairList_canonListCode c p).mp hp
  exact hcond

theorem forall_lt_decodeQPairList_canonCode (c : ℕ) :
    ∀ p ∈ decodeQPairList (canonCode c), p.1 < p.2 := by
  unfold canonCode
  by_cases hz : canonListCode c = 0
  · have hzero : isZero (canonListCode c) = 1 := by rw [hz]; exact (isZero_eq_one_iff 0).mpr rfl
    rw [hzero, selectFn_one]
    intro p hp
    rw [decodeQPairList_masterCode, List.mem_singleton] at hp
    rw [hp]; norm_num
  · have hzero : isZero (canonListCode c) = 0 := by
      by_contra hcontra
      have h1 := isZero_le_one (canonListCode c)
      exact hz ((isZero_eq_one_iff _).mp (by omega))
    rw [hzero, selectFn_zero]
    exact forall_lt_decodeQPairList_canonListCode c

theorem U_mem_union_UX (n m : ℕ) : U.mem (UX n ∪ UX m) := by
  obtain ⟨-, hne1, hsub1⟩ := U_mem_UX n
  obtain ⟨-, -, hsub2⟩ := U_mem_UX m
  exact ⟨⟨decodeQPairList (canonCode n) ++ decodeQPairList (canonCode m),
      (presentedIntervals.append _ _).symm⟩, hne1.mono Set.subset_union_left,
    Set.union_subset hsub1 hsub2⟩

end DomainTheory.NeighbourhoodSystems
