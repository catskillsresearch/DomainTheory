module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ratCodes
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_29
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ExampleC_le_B
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_12

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

def decodeRatPair (c : ℕ) : ℚ × ℚ := (decodeRat c.unpair.1, decodeRat c.unpair.2)

def encodeRatPair (p : ℚ × ℚ) : ℕ := Nat.pair (encodeRat p.1) (encodeRat p.2)

@[simp] theorem decodeRatPair_encodeRatPair (p : ℚ × ℚ) : decodeRatPair (encodeRatPair p) = p := by
  unfold decodeRatPair encodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_encodeRat]

def decodeQPairList (c : ℕ) : List (ℚ × ℚ) := (decodeList c).map decodeRatPair

def encodeQPairList (L : List (ℚ × ℚ)) : ℕ := encodeList (L.map encodeRatPair)

@[simp] theorem decodeQPairList_encodeQPairList (L : List (ℚ × ℚ)) :
    decodeQPairList (encodeQPairList L) = L := by
  unfold decodeQPairList encodeQPairList
  rw [decodeList_encodeList, List.map_map]
  simp only [Function.comp_def, decodeRatPair_encodeRatPair, List.map_id_fun', id]

def diffOneCode (t : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1.unpair.1)))
    (Nat.pair (Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2))
      t.unpair.2.unpair.2) 0 + 1) + 1

def diffSingleCode (accL q : ℕ) : ℕ := flatMapCode diffOneCode q accL

def diffAllStep (w : ℕ) : ℕ := diffSingleCode w.unpair.2.unpair.1 w.unpair.1

def diffAllCode (pc L2 : ℕ) : ℕ := foldCode diffAllStep 0 (Nat.pair pc 0 + 1) L2

def diffCode (c1 c2 : ℕ) : ℕ := flatMapCode (fun t => diffAllCode t.unpair.2 t.unpair.1) c2 c1

def qpCombineBop (t : ℕ) : ℕ :=
  Nat.pair (ratMaxCode (Nat.pair t.unpair.1.unpair.1 t.unpair.2.unpair.1))
    (ratMinCode (Nat.pair t.unpair.1.unpair.2 t.unpair.2.unpair.2))

def combineCode (c1 c2 : ℕ) : ℕ := crossCombine qpCombineBop c1 c2

def qpNonemptyBop (e : ℕ) : ℕ := ratLtCode (Nat.pair e.unpair.1 e.unpair.2)

def qpNonemptyChar (c : ℕ) : ℕ := existsListChar (fun t => qpNonemptyBop t.unpair.1) 0 c

theorem decodeQPairList_diffOneCode (qc pc : ℕ) :
    decodeQPairList (diffOneCode (Nat.pair qc pc)) = diffOneList (decodeRatPair pc) (decodeRatPair qc) := by
  unfold diffOneCode decodeQPairList diffOneList decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd, decodeList_succ, decodeList_zero, List.map_cons,
    List.map_nil]
  rw [decodeRat_ratMinCode, decodeRat_ratMaxCode]

theorem mem_decodeQPairList_flatMapCode (f : ℕ → ℕ) (x c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (flatMapCode f x c) ↔ ∃ y ∈ decodeList c, p ∈ decodeQPairList (f (Nat.pair x y)) := by
  unfold decodeQPairList
  rw [List.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_decodeList_flatMapCode] at hz
    obtain ⟨y, hy, hz'⟩ := hz
    exact ⟨y, hy, List.mem_map_of_mem hz'⟩
  · rintro ⟨y, hy, hp⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    exact ⟨e, (mem_decodeList_flatMapCode (f := f) x c e).mpr ⟨y, hy, he⟩, rfl⟩

theorem mem_decodeQPairList_diffSingleCode (accL q : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (diffSingleCode accL q) ↔ p ∈ diffSingleList (decodeQPairList accL) (decodeRatPair q) := by
  unfold diffSingleCode
  rw [mem_decodeQPairList_flatMapCode]
  simp only [decodeQPairList_diffOneCode]
  unfold diffSingleList decodeQPairList
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨y, hy, hp⟩; exact ⟨decodeRatPair y, ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p', ⟨y, hy, rfl⟩, hp⟩; exact ⟨y, hy, hp⟩

theorem presentedIntervals_decodeQPairList_diffSingleCode (accL q : ℕ) :
    presentedIntervals (decodeQPairList (diffSingleCode accL q))
      = presentedIntervals (decodeQPairList accL) \ Set.Ico (decodeRatPair q).1 (decodeRatPair q).2 := by
  rw [presentedIntervals.congr (mem_decodeQPairList_diffSingleCode accL q), presentedIntervals.diffSingleList]

theorem diffAllStep_eq (acc x : ℕ) : diffAllStep (Nat.pair x (Nat.pair acc 0)) = diffSingleCode acc x := by
  unfold diffAllStep; simp only [unpair_pair_fst, unpair_pair_snd]

theorem presentedIntervals_decodeQPairList_foldl_diffAllStep (L2list : List ℕ) :
    ∀ acc : ℕ, presentedIntervals (decodeQPairList
        (List.foldl (fun acc x => diffAllStep (Nat.pair x (Nat.pair acc 0))) acc L2list))
      = presentedIntervals (decodeQPairList acc) \ presentedIntervals (L2list.map decodeRatPair) := by
  induction L2list with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    rw [List.foldl_cons, diffAllStep_eq, ih (diffSingleCode acc a),
      presentedIntervals_decodeQPairList_diffSingleCode, List.map_cons, presentedIntervals.cons,
      Set.sdiff_sdiff]

theorem presentedIntervals_decodeQPairList_diffAllCode (pc L2 : ℕ) :
    presentedIntervals (decodeQPairList (diffAllCode pc L2))
      = Set.Ico (decodeRatPair pc).1 (decodeRatPair pc).2 \ presentedIntervals (decodeQPairList L2) := by
  unfold diffAllCode
  rw [foldCode_eq', presentedIntervals_decodeQPairList_foldl_diffAllStep]
  unfold decodeQPairList
  simp only [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero, List.map_cons,
    List.map_nil, presentedIntervals.cons, presentedIntervals.nil, Set.union_empty]

theorem mem_decodeQPairList_diffCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (diffCode c1 c2) ↔ ∃ y ∈ decodeList c1, p ∈ decodeQPairList (diffAllCode y c2) := by
  unfold diffCode
  rw [mem_decodeQPairList_flatMapCode]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem presentedIntervals_decodeQPairList_flatMap_diffAllCode (c1list : List ℕ) (c2 : ℕ) :
    presentedIntervals (c1list.flatMap (fun y => decodeQPairList (diffAllCode y c2)))
      = presentedIntervals (c1list.map decodeRatPair) \ presentedIntervals (decodeQPairList c2) := by
  induction c1list with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_cons, presentedIntervals.append,
      presentedIntervals_decodeQPairList_diffAllCode, ih, presentedIntervals.cons,
      Set.union_sdiff_distrib]

theorem presentedIntervals_decodeQPairList_diffCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (diffCode c1 c2))
      = presentedIntervals (decodeQPairList c1) \ presentedIntervals (decodeQPairList c2) := by
  rw [presentedIntervals.congr
      (fun p => (mem_decodeQPairList_diffCode c1 c2 p).trans (List.mem_flatMap).symm),
    presentedIntervals_decodeQPairList_flatMap_diffAllCode]
  rfl

theorem presentedIntervals_nonempty_iff (L : List (ℚ × ℚ)) :
    (presentedIntervals L).Nonempty ↔ ∃ p ∈ L, p.1 < p.2 := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨p, hp, hx1, hx2⟩ := presentedIntervals.mem.mp hx
    exact ⟨p, hp, lt_of_le_of_lt hx1 hx2⟩
  · rintro ⟨p, hp, hlt⟩
    exact ⟨p.1, presentedIntervals.mem.mpr ⟨p, hp, le_refl _, hlt⟩⟩

theorem decodeRatPair_qpCombineBop (e1 e2 : ℕ) :
    decodeRatPair (qpCombineBop (Nat.pair e1 e2))
      = ((decodeRatPair e1).1 ⊔ (decodeRatPair e2).1, (decodeRatPair e1).2 ⊓ (decodeRatPair e2).2) := by
  unfold qpCombineBop decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [decodeRat_ratMaxCode, decodeRat_ratMinCode]

theorem mem_combineIntervals {L1 L2 : List (ℚ × ℚ)} {p : ℚ × ℚ} :
    p ∈ combineIntervals L1 L2 ↔ ∃ p1 ∈ L1, ∃ p2 ∈ L2, p = (p1.1 ⊔ p2.1, p1.2 ⊓ p2.2) := by
  unfold combineIntervals
  rw [List.mem_flatMap]
  simp only [List.mem_map, eq_comm]

theorem mem_decodeQPairList (c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList c ↔ ∃ e ∈ decodeList c, p = decodeRatPair e := by
  unfold decodeQPairList; rw [List.mem_map]; simp [eq_comm]

theorem mem_decodeQPairList_combineCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (combineCode c1 c2) ↔
      ∃ p1 ∈ decodeQPairList c1, ∃ p2 ∈ decodeQPairList c2, p = (p1.1 ⊔ p2.1, p1.2 ⊓ p2.2) := by
  unfold decodeQPairList combineCode
  rw [List.mem_map]
  constructor
  · rintro ⟨z, hz, hpz⟩
    rw [mem_decodeList_crossCombine] at hz
    obtain ⟨e1, he1, e2, he2, hze⟩ := hz
    refine ⟨decodeRatPair e1, List.mem_map_of_mem he1, decodeRatPair e2, List.mem_map_of_mem he2, ?_⟩
    rw [← hpz, hze, decodeRatPair_qpCombineBop]
  · rintro ⟨p1, hp1, p2, hp2, hp⟩
    obtain ⟨e1, he1, he1'⟩ := List.mem_map.mp hp1
    obtain ⟨e2, he2, he2'⟩ := List.mem_map.mp hp2
    refine ⟨qpCombineBop (Nat.pair e1 e2),
      (mem_decodeList_crossCombine (bop := qpCombineBop) c1 c2 _).mpr ⟨e1, he1, e2, he2, rfl⟩, ?_⟩
    rw [decodeRatPair_qpCombineBop, he1', he2', hp]

theorem presentedIntervals_decodeQPairList_combineCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (combineCode c1 c2))
      = presentedIntervals (decodeQPairList c1) ∩ presentedIntervals (decodeQPairList c2) := by
  rw [presentedIntervals.inter]
  apply presentedIntervals.congr
  intro p
  rw [mem_decodeQPairList_combineCode, mem_combineIntervals]

theorem presentedIntervals_decodeQPairList_subset_iff (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList c1) ⊆ presentedIntervals (decodeQPairList c2) ↔
      ¬ (presentedIntervals (decodeQPairList (diffCode c1 c2))).Nonempty := by
  rw [presentedIntervals_decodeQPairList_diffCode, Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty]

theorem primrec_diffOneCode : Nat.Primrec diffOneCode := by
  have ha : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hb : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hc : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hd : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.left
  have hleft : Nat.Primrec (fun t : ℕ =>
      Nat.pair t.unpair.2.unpair.1 (ratMinCode (Nat.pair t.unpair.2.unpair.2 t.unpair.1.unpair.1))) :=
    ha.pair (primrec_ratMinCode.comp (hb.pair hc))
  have hright : Nat.Primrec (fun t : ℕ =>
      Nat.pair (ratMaxCode (Nat.pair t.unpair.2.unpair.1 t.unpair.1.unpair.2)) t.unpair.2.unpair.2) :=
    (primrec_ratMaxCode.comp (ha.pair hd)).pair hb
  exact (Nat.Primrec.succ.comp (hleft.pair
    (Nat.Primrec.succ.comp (hright.pair (Nat.Primrec.const 0))))).of_eq fun _ => rfl

theorem primrec_diffSingleCode : Nat.Primrec (fun t : ℕ => diffSingleCode t.unpair.1 t.unpair.2) := by
  unfold diffSingleCode
  exact ((primrec_flatMapCode primrec_diffOneCode).comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_diffAllStep : Nat.Primrec diffAllStep := by
  unfold diffAllStep
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hq : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  exact (primrec_diffSingleCode.comp (hacc.pair hq)).of_eq fun w => by
    simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_diffAllCode : Nat.Primrec (fun t : ℕ => diffAllCode t.unpair.1 t.unpair.2) :=
  (primrec_foldCode primrec_diffAllStep (Nat.Primrec.const 0)
    (Nat.Primrec.succ.comp (Nat.Primrec.left.pair (Nat.Primrec.const 0)))
    Nat.Primrec.right).of_eq fun _ => rfl

theorem primrec_diffCode : Nat.Primrec (fun t : ℕ => diffCode t.unpair.1 t.unpair.2) := by
  unfold diffCode
  have hf : Nat.Primrec (fun t : ℕ => diffAllCode t.unpair.2 t.unpair.1) :=
    (primrec_diffAllCode.comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact ((primrec_flatMapCode hf).comp (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq fun t => by
    simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_qpCombineBop : Nat.Primrec qpCombineBop := by
  have h11 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have h12 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have h21 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have h22 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact ((primrec_ratMaxCode.comp (h11.pair h21)).pair
    (primrec_ratMinCode.comp (h12.pair h22))).of_eq fun _ => rfl

theorem primrec_combineCode : Nat.Primrec (fun t => combineCode t.unpair.1 t.unpair.2) :=
  primrec_crossCombine primrec_qpCombineBop

theorem primrec_qpNonemptyBop : Nat.Primrec qpNonemptyBop :=
  primrec_ratLtCode.comp (Nat.Primrec.left.pair Nat.Primrec.right)

theorem primrec_qpNonemptyChar : Nat.Primrec qpNonemptyChar := by
  have hg : Nat.Primrec (fun t : ℕ => qpNonemptyBop t.unpair.1) :=
    primrec_qpNonemptyBop.comp Nat.Primrec.left
  exact ((primrec_existsListChar hg).comp (primrec_id.pair (Nat.Primrec.const 0))).of_eq
    fun c => by
      unfold qpNonemptyChar
      simp only [id, unpair_pair_fst, unpair_pair_snd]

theorem qpNonemptyBop_eq_one_iff (e : ℕ) :
    qpNonemptyBop e = 1 ↔ (decodeRatPair e).1 < (decodeRatPair e).2 := by
  unfold qpNonemptyBop decodeRatPair; exact ratLtCode_eq_one_iff e.unpair.1 e.unpair.2

theorem qpNonemptyChar_eq_one_iff (c : ℕ) :
    qpNonemptyChar c = 1 ↔ ∃ e ∈ decodeList c, (decodeRatPair e).1 < (decodeRatPair e).2 := by
  unfold qpNonemptyChar
  rw [existsListChar_eq_one_iff]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  rw [unpair_pair_fst, qpNonemptyBop_eq_one_iff]

theorem presentedIntervals_decodeQPairList_nonempty_iff (c : ℕ) :
    (presentedIntervals (decodeQPairList c)).Nonempty ↔ qpNonemptyChar c = 1 := by
  rw [presentedIntervals_nonempty_iff, qpNonemptyChar_eq_one_iff]
  constructor
  · rintro ⟨p, hp, hlt⟩
    obtain ⟨e, he, rfl⟩ := (mem_decodeQPairList c p).mp hp
    exact ⟨e, he, hlt⟩
  · rintro ⟨e, he, hlt⟩
    exact ⟨decodeRatPair e, (mem_decodeQPairList c (decodeRatPair e)).mpr ⟨e, he, rfl⟩, hlt⟩

theorem qpNonemptyChar_le_one (c : ℕ) : qpNonemptyChar c ≤ 1 := existsListChar_le_one _ 0 c

theorem recDecidable_presentedIntervals_nonempty :
    RecDecidable (fun c => (presentedIntervals (decodeQPairList c)).Nonempty) :=
  RecDecidable.of_zero_one_char primrec_qpNonemptyChar
    (fun c => by have := qpNonemptyChar_le_one c; omega)
    presentedIntervals_decodeQPairList_nonempty_iff

theorem recDecidable₂_presentedIntervals_subset :
    RecDecidable₂ (fun c1 c2 =>
      presentedIntervals (decodeQPairList c1) ⊆ presentedIntervals (decodeQPairList c2)) := by
  unfold RecDecidable₂
  refine RecDecidable.of_iff (fun t => ?_)
    (recDecidable_presentedIntervals_nonempty.comp primrec_diffCode).not
  exact presentedIntervals_decodeQPairList_subset_iff t.unpair.1 t.unpair.2

theorem recDecidable₂_presentedIntervals_eq :
    RecDecidable₂ (fun c1 c2 =>
      presentedIntervals (decodeQPairList c1) = presentedIntervals (decodeQPairList c2)) := by
  unfold RecDecidable₂
  refine RecDecidable.of_iff (fun t => ?_)
    (recDecidable₂_presentedIntervals_subset.and recDecidable₂_presentedIntervals_subset.swap)
  exact Set.Subset.antisymm_iff

theorem mem_decodeQPairList_appendCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (Domain.Recursive.appendCode c1 c2) ↔ p ∈ decodeQPairList c1 ∨ p ∈ decodeQPairList c2 := by
  simp only [mem_decodeQPairList, mem_decodeList_appendCode]
  constructor
  · rintro ⟨v, (hv | hv), rfl⟩
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr ⟨v, hv, rfl⟩
  · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact ⟨v, Or.inl hv, rfl⟩
    · exact ⟨v, Or.inr hv, rfl⟩

theorem presentedIntervals_decodeQPairList_appendCode (c1 c2 : ℕ) :
    presentedIntervals (decodeQPairList (Domain.Recursive.appendCode c1 c2))
      = presentedIntervals (decodeQPairList c1) ∪ presentedIntervals (decodeQPairList c2) := by
  ext x
  simp only [presentedIntervals.mem, Set.mem_union]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    rcases (mem_decodeQPairList_appendCode c1 c2 p).mp hp with hp' | hp'
    · exact Or.inl ⟨p, hp', h1, h2⟩
    · exact Or.inr ⟨p, hp', h1, h2⟩
  · rintro (⟨p, hp, h1, h2⟩ | ⟨p, hp, h1, h2⟩)
    · exact ⟨p, (mem_decodeQPairList_appendCode c1 c2 p).mpr (Or.inl hp), h1, h2⟩
    · exact ⟨p, (mem_decodeQPairList_appendCode c1 c2 p).mpr (Or.inr hp), h1, h2⟩

end DomainTheory.NeighbourhoodSystems
