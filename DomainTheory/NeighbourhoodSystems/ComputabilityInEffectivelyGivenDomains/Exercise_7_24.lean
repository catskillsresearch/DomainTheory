module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_12
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_3
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724
open NeighborhoodSystem Domain.Recursive

section

abbrev Gamma : Type := List ℕ ⊕ (ℕ → ℕ)
end

section

def star : Gamma := Sum.inl []
end

section

def streamCons (i : ℕ) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => i
  | n + 1 => s n
end

section
@[simp] theorem streamCons_zero (i : ℕ) (s : ℕ → ℕ) : streamCons i s 0 = i := rfl
end

section
@[simp] theorem streamCons_succ (i : ℕ) (s : ℕ → ℕ) (n : ℕ) : streamCons i s (n + 1) = s n := rfl
end

section

def cons (i : ℕ) : Gamma → Gamma
  | .inl l => .inl (i :: l)
  | .inr s => .inr (streamCons i s)
end

section

def consSet (i : ℕ) (X : Set Gamma) : Set Gamma := {z | ∃ γ ∈ X, z = cons i γ}
end

section

theorem cons_injective {i j : ℕ} {γ δ : Gamma} (h : cons i γ = cons j δ) : i = j ∧ γ = δ := by
  cases γ with
  | inl l =>
    cases δ with
    | inl l' =>
      simp only [cons, Sum.inl.injEq, List.cons.injEq] at h
      exact ⟨h.1, by rw [h.2]⟩
    | inr s' => simp [cons] at h
  | inr s =>
    cases δ with
    | inl l' => simp [cons] at h
    | inr s' =>
      have heq : streamCons i s = streamCons j s' := by simpa [cons] using h
      have hi : i = j := by simpa using congrFun heq 0
      refine ⟨hi, ?_⟩
      have hs : s = s' := funext fun n => by simpa using congrFun heq (n + 1)
      rw [hs]
end

section
@[simp] theorem mem_consSet {i : ℕ} {X : Set Gamma} {z : Gamma} :
    z ∈ consSet i X ↔ ∃ γ ∈ X, z = cons i γ := Iff.rfl
end

section
@[simp] theorem consSet_empty (i : ℕ) : consSet i (∅ : Set Gamma) = ∅ := by
  ext z; simp [mem_consSet]
end

section
theorem consSet_inter (i : ℕ) (X X' : Set Gamma) :
    consSet i X ∩ consSet i X' = consSet i (X ∩ X') := by
  ext z
  simp only [Set.mem_inter_iff, mem_consSet]
  constructor
  · rintro ⟨⟨γ, hγ, rfl⟩, γ', hγ', heq⟩
    obtain ⟨-, hγγ'⟩ := cons_injective heq
    exact ⟨γ, ⟨hγ, hγγ' ▸ hγ'⟩, rfl⟩
  · rintro ⟨γ, ⟨hγ, hγ'⟩, rfl⟩
    exact ⟨⟨γ, hγ, rfl⟩, ⟨γ, hγ', rfl⟩⟩
end

section
theorem consSet_inter_ne {i j : ℕ} (h : i ≠ j) (X Y : Set Gamma) :
    consSet i X ∩ consSet j Y = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, mem_consSet, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨γ, -, rfl⟩ ⟨γ', -, heq⟩
  exact h (cons_injective heq).1
end

section
theorem consSet_nonempty {i : ℕ} {X : Set Gamma} (h : X.Nonempty) : (consSet i X).Nonempty := by
  obtain ⟨γ, hγ⟩ := h; exact ⟨cons i γ, γ, hγ, rfl⟩
end

section
theorem consSet_subset_of_subset {i : ℕ} {X X' : Set Gamma} (h : X ⊆ X') :
    consSet i X ⊆ consSet i X' := by
  rintro z ⟨γ, hγ, rfl⟩; exact ⟨γ, h hγ, rfl⟩
end

section

theorem consSet_subset {i : ℕ} {X X' : Set Gamma} :
    consSet i X ⊆ consSet i X' ↔ X ⊆ X' := by
  refine ⟨fun h γ hγ => ?_, consSet_subset_of_subset⟩
  obtain ⟨γ', hγ', heq⟩ := h ⟨γ, hγ, rfl⟩
  rwa [(cons_injective heq.symm).2] at hγ'
end

section

def nbhd : List ℕ → Set Gamma
  | [] => Set.univ
  | i :: l => consSet i (nbhd l)
end

section
@[simp] theorem nbhd_nil : nbhd [] = (Set.univ : Set Gamma) := rfl
end

section
@[simp] theorem nbhd_cons (i : ℕ) (l : List ℕ) : nbhd (i :: l) = consSet i (nbhd l) := rfl
end

section

def Lmem (X : Set Gamma) : Prop := ∃ l, X = nbhd l
end

section
@[simp] theorem mem_nbhd (l : List ℕ) : Lmem (nbhd l) := ⟨l, rfl⟩
end

section

theorem L_nestedOrDisjoint : NestedOrDisjoint Lmem := by
  rintro X Y ⟨l, rfl⟩ ⟨l', rfl⟩
  induction l generalizing l' with
  | nil => exact Or.inr (Or.inl (by simp))
  | cons i s ih =>
    cases l' with
    | nil => exact Or.inl (by simp)
    | cons j t =>
      by_cases hij : i = j
      · subst hij
        rcases ih t with h1 | h2 | h3
        · exact Or.inl (by rw [nbhd_cons, nbhd_cons]; exact consSet_subset_of_subset h1)
        · exact Or.inr (Or.inl (by rw [nbhd_cons, nbhd_cons]; exact consSet_subset_of_subset h2))
        · exact Or.inr (Or.inr (by rw [nbhd_cons, nbhd_cons, consSet_inter, h3, consSet_empty]))
      · exact Or.inr (Or.inr (by rw [nbhd_cons, nbhd_cons]; exact consSet_inter_ne hij _ _))
end

end DomainTheory.NeighbourhoodSystems.Exercise724

section
namespace DomainTheory.NeighbourhoodSystems.Exercise724
open NeighborhoodSystem Domain.Recursive
section

abbrev L : NeighborhoodSystem Gamma :=
  NeighborhoodSystem.ofNestedOrDisjoint Lmem Set.univ Set.univ_nonempty
    (mem_nbhd []) L_nestedOrDisjoint
    (fun {X} _ => Set.subset_univ X)
end

section

def Lenum (n : ℕ) : Set Gamma := nbhd (decodeList n)
end

section
@[simp] theorem Lenum_mem (n : ℕ) : Lmem (Lenum n) := mem_nbhd (decodeList n)
end

section
theorem Lenum_surj {Y : Set Gamma} (hY : Lmem Y) : ∃ n, Lenum n = Y := by
  obtain ⟨l, rfl⟩ := hY
  exact ⟨encodeList l, by unfold Lenum; rw [decodeList_encodeList]⟩
end

section

theorem Lenum_zero : Lenum 0 = Set.univ := by unfold Lenum; rw [decodeList_zero]; rfl
end

section

def isPrefixChar (m n : ℕ) : ℕ := listEqChar (takeCode (listLenChar m) n) m
end

section

def LenumConsChar (n m : ℕ) : ℕ :=
  isPrefixChar m n + isPrefixChar n m - isPrefixChar m n * isPrefixChar n m
end

section

def LenumConsCharP (t : ℕ) : ℕ := LenumConsChar t.unpair.1 t.unpair.2
end

section
def LenumInter (n m : ℕ) : ℕ := selectFn (isPrefixChar m n) n m
end

section

def LenumInterEqChar (n m k : ℕ) : ℕ :=
  mulBit (isPrefixChar m n) (listEqChar k n) + mulBit (isPrefixChar n m) (listEqChar k m)
    - mulBit (isPrefixChar m n) (listEqChar k n) * mulBit (isPrefixChar n m) (listEqChar k m)
end

section

def LenumInterEqCharP (t : ℕ) : ℕ :=
  LenumInterEqChar t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2
end

section
theorem isPrefixChar_eq_one_iff (m n : ℕ) :
    isPrefixChar m n = 1 ↔ decodeList m <+: decodeList n := by
  unfold isPrefixChar
  rw [listEqChar_eq_one_iff, takeCode_eq, listLenChar_eq, List.prefix_iff_eq_take]
  exact eq_comm
end

section
theorem isPrefixChar_le_one (m n : ℕ) : isPrefixChar m n ≤ 1 := listEqChar_le_one _ _
end

section
theorem isPrefixChar_eq_zero_or_one (m n : ℕ) :
    isPrefixChar m n = 0 ∨ isPrefixChar m n = 1 := by
  have := isPrefixChar_le_one m n; omega
end

section
theorem LenumConsChar_eq_one_iff (n m : ℕ) :
    LenumConsChar n m = 1 ↔ isPrefixChar m n = 1 ∨ isPrefixChar n m = 1 := by
  unfold LenumConsChar
  rcases isPrefixChar_eq_zero_or_one m n with ha | ha <;>
    rcases isPrefixChar_eq_zero_or_one n m with hb | hb <;> simp [ha, hb]
end

section
theorem LenumConsChar_le_one (n m : ℕ) : LenumConsChar n m ≤ 1 := by
  unfold LenumConsChar
  rcases isPrefixChar_eq_zero_or_one m n with ha | ha <;>
    rcases isPrefixChar_eq_zero_or_one n m with hb | hb <;> simp [ha, hb]
end

section
theorem LenumConsCharP_le_one (t : ℕ) : LenumConsCharP t ≤ 1 :=
  LenumConsChar_le_one _ _
end

section
theorem mulBit_eq_zero_or_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) :
    mulBit a b = 0 ∨ mulBit a b = 1 := by
  have := mulBit_le_one ha hb; omega
end

section
theorem LenumInterEqChar_eq_one_iff (n m k : ℕ) :
    LenumInterEqChar n m k = 1 ↔
      (isPrefixChar m n = 1 ∧ decodeList k = decodeList n) ∨
      (isPrefixChar n m = 1 ∧ decodeList k = decodeList m) := by
  have hstep : LenumInterEqChar n m k = 1 ↔
      mulBit (isPrefixChar m n) (listEqChar k n) = 1 ∨
      mulBit (isPrefixChar n m) (listEqChar k m) = 1 := by
    unfold LenumInterEqChar
    rcases mulBit_eq_zero_or_one (isPrefixChar_le_one m n) (listEqChar_le_one k n) with ha | ha <;>
      rcases mulBit_eq_zero_or_one (isPrefixChar_le_one n m) (listEqChar_le_one k m) with hb | hb <;>
        simp [ha, hb]
  rw [hstep, mulBit_eq_one_iff, mulBit_eq_one_iff, listEqChar_eq_one_iff, listEqChar_eq_one_iff]
end

section
theorem LenumInterEqChar_le_one (n m k : ℕ) : LenumInterEqChar n m k ≤ 1 := by
  unfold LenumInterEqChar
  rcases mulBit_eq_zero_or_one (isPrefixChar_le_one m n) (listEqChar_le_one k n) with ha | ha <;>
    rcases mulBit_eq_zero_or_one (isPrefixChar_le_one n m) (listEqChar_le_one k m) with hb | hb <;>
      simp [ha, hb]
end

section
theorem LenumInterEqCharP_le_one (t : ℕ) : LenumInterEqCharP t ≤ 1 :=
  LenumInterEqChar_le_one _ _ _
end

section
theorem nbhd_nonempty : ∀ l : List ℕ, (nbhd l).Nonempty
  | [] => ⟨star, trivial⟩
  | _ :: l => consSet_nonempty (nbhd_nonempty l)
end

section
theorem primrec_isPrefixChar : Nat.Primrec (fun t => isPrefixChar t.unpair.1 t.unpair.2) := by
  have hlen : Nat.Primrec (fun t : ℕ => listLenChar t.unpair.1) := primrec_listLenChar.comp Nat.Primrec.left
  have htake : Nat.Primrec (fun t : ℕ => takeCode (listLenChar t.unpair.1) t.unpair.2) :=
    (primrec_takeCode.comp (Nat.Primrec.pair hlen Nat.Primrec.right)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_listEqChar.comp (Nat.Primrec.pair htake Nat.Primrec.left)).of_eq fun t => by
    simp only [isPrefixChar, unpair_pair_fst, unpair_pair_snd]
end

section
theorem primrec_LenumInterEqChar :
    Nat.Primrec (fun t => LenumInterEqChar t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hpmn : Nat.Primrec (fun t : ℕ => isPrefixChar t.unpair.2.unpair.1 t.unpair.1) :=
    (primrec_isPrefixChar.comp (Nat.Primrec.pair hm hn)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hpnm : Nat.Primrec (fun t : ℕ => isPrefixChar t.unpair.1 t.unpair.2.unpair.1) :=
    (primrec_isPrefixChar.comp (Nat.Primrec.pair hn hm)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hekn : Nat.Primrec (fun t : ℕ => listEqChar t.unpair.2.unpair.2 t.unpair.1) :=
    (primrec_listEqChar.comp (Nat.Primrec.pair hk hn)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hekm : Nat.Primrec (fun t : ℕ => listEqChar t.unpair.2.unpair.2 t.unpair.2.unpair.1) :=
    (primrec_listEqChar.comp (Nat.Primrec.pair hk hm)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have ha : Nat.Primrec (fun t : ℕ => mulBit (isPrefixChar t.unpair.2.unpair.1 t.unpair.1)
      (listEqChar t.unpair.2.unpair.2 t.unpair.1)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair hpmn hekn)).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hb : Nat.Primrec (fun t : ℕ => mulBit (isPrefixChar t.unpair.1 t.unpair.2.unpair.1)
      (listEqChar t.unpair.2.unpair.2 t.unpair.2.unpair.1)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair hpnm hekm)).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_sub₂ (primrec_add₂ ha hb) (primrec_mul₂ ha hb)).of_eq fun t => by
    simp only [LenumInterEqChar]
end

section
theorem primrec_LenumInterEqCharP : Nat.Primrec LenumInterEqCharP :=
  primrec_LenumInterEqChar.of_eq fun t => by simp only [LenumInterEqCharP]
end

section

theorem primrec_isPrefixChar_swap :
    Nat.Primrec (fun t => isPrefixChar t.unpair.2 t.unpair.1) :=
  (primrec_isPrefixChar.comp (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
end

section
theorem primrec_LenumConsChar :
    Nat.Primrec (fun t => LenumConsChar t.unpair.1 t.unpair.2) := by
  have ha : Nat.Primrec (fun t : ℕ => isPrefixChar t.unpair.2 t.unpair.1) :=
    primrec_isPrefixChar_swap
  have hb : Nat.Primrec (fun t : ℕ => isPrefixChar t.unpair.1 t.unpair.2) := primrec_isPrefixChar
  exact (primrec_sub₂ (primrec_add₂ ha hb) (primrec_mul₂ ha hb)).of_eq fun t => by
    simp only [LenumConsChar]
end

section
theorem primrec_LenumConsCharP : Nat.Primrec LenumConsCharP :=
  primrec_LenumConsChar.of_eq fun t => by simp only [LenumConsCharP]
end

section
theorem primrec_LenumInter : Nat.Primrec (fun t => LenumInter t.unpair.1 t.unpair.2) :=
  (primrec_selectFn primrec_isPrefixChar_swap Nat.Primrec.left Nat.Primrec.right).of_eq
    fun t => by simp only [LenumInter]
end

section

theorem star_ne_cons (i : ℕ) (γ : Gamma) : star ≠ cons i γ := by
  cases γ <;> simp [star, cons]
end

section
theorem star_not_mem_consSet (i : ℕ) (X : Set Gamma) : star ∉ consSet i X := by
  rintro ⟨γ, -, heq⟩; exact star_ne_cons i γ heq
end

section

theorem nbhd_subset_iff : ∀ (l l' : List ℕ), nbhd l ⊆ nbhd l' ↔ l' <+: l := by
  intro l
  induction l with
  | nil =>
    intro l'
    cases l' with
    | nil => simp
    | cons j t =>
      constructor
      · intro h
        exact absurd (h (Set.mem_univ star)) (by rw [nbhd_cons]; exact star_not_mem_consSet j (nbhd t))
      · rintro ⟨u, hu⟩
        simp at hu
  | cons i s ih =>
    intro l'
    cases l' with
    | nil => simp [nbhd_cons]
    | cons j t =>
      by_cases hij : i = j
      · subst hij
        rw [nbhd_cons, nbhd_cons, consSet_subset, ih t, List.cons_prefix_cons]
        simp
      · constructor
        · intro h
          exfalso
          obtain ⟨γ, hγ⟩ := nbhd_nonempty s
          have hmem : cons i γ ∈ consSet j (nbhd t) := h ⟨γ, hγ, rfl⟩
          obtain ⟨γ', -, heq⟩ := hmem
          exact hij (cons_injective heq).1
        · intro h
          rw [List.cons_prefix_cons] at h
          exact absurd h.1.symm hij
end

section

theorem Lenum_subset_iff (n m : ℕ) : Lenum n ⊆ Lenum m ↔ isPrefixChar m n = 1 := by
  unfold Lenum; rw [nbhd_subset_iff, isPrefixChar_eq_one_iff]
end

section

theorem Lenum_cons_iff (n m : ℕ) :
    (∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) ↔ isPrefixChar m n = 1 ∨ isPrefixChar n m = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    rcases L_nestedOrDisjoint (mem_nbhd (decodeList n)) (mem_nbhd (decodeList m)) with h | h | h
    · exact Or.inl ((isPrefixChar_eq_one_iff m n).mpr ((nbhd_subset_iff _ _).mp h))
    · exact Or.inr ((isPrefixChar_eq_one_iff n m).mpr ((nbhd_subset_iff _ _).mp h))
    · exfalso
      unfold Lenum at hk
      obtain ⟨t, ht⟩ := nbhd_nonempty (decodeList k)
      exact Set.notMem_empty t (h ▸ hk ht)
  · rintro (hp | hp)
    · exact ⟨n, Set.subset_inter subset_rfl ((Lenum_subset_iff n m).mpr hp)⟩
    · exact ⟨m, Set.subset_inter ((Lenum_subset_iff m n).mpr hp) subset_rfl⟩
end

section
theorem LenumInter_spec {n m : ℕ} (h : ∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) :
    Lenum (LenumInter n m) = Lenum n ∩ Lenum m := by
  unfold LenumInter
  rcases isPrefixChar_eq_zero_or_one m n with h0 | h1
  · rw [h0, selectFn_zero]
    have hp : isPrefixChar n m = 1 := by
      rcases (Lenum_cons_iff n m).mp h with hp | hp
      · rw [h0] at hp; exact absurd hp (by decide)
      · exact hp
    exact (Set.inter_eq_right.mpr ((Lenum_subset_iff m n).mpr hp)).symm
  · rw [h1, selectFn_one]
    exact (Set.inter_eq_left.mpr ((Lenum_subset_iff n m).mpr h1)).symm
end

section
theorem Lenum_cons_charP_eq_one_iff (n m : ℕ) :
    (∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) ↔ LenumConsCharP (Nat.pair n m) = 1 := by
  unfold LenumConsCharP
  rw [unpair_pair_fst, unpair_pair_snd, LenumConsChar_eq_one_iff]
  exact Lenum_cons_iff n m
end

section

theorem Lenum_cons_computable : RecDecidable₂ (fun n m => ∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) :=
  RecDecidable₂.of_paired_zero_one_char primrec_LenumConsCharP
    (fun t => by have := LenumConsCharP_le_one t; omega)
    Lenum_cons_charP_eq_one_iff
end

section

theorem nbhd_injective {l l' : List ℕ} (h : nbhd l = nbhd l') : l = l' := by
  have h1 : l' <+: l := (nbhd_subset_iff l l').mp h.subset
  have h2 : l <+: l' := (nbhd_subset_iff l' l).mp h.symm.subset
  exact (h1.eq_of_length (h1.length_le.antisymm h2.length_le)).symm
end

section

theorem Lenum_interEq_iff (n m k : ℕ) :
    Lenum n ∩ Lenum m = Lenum k ↔
      (isPrefixChar m n = 1 ∧ decodeList k = decodeList n) ∨
      (isPrefixChar n m = 1 ∧ decodeList k = decodeList m) := by
  unfold Lenum
  rcases L_nestedOrDisjoint (mem_nbhd (decodeList n)) (mem_nbhd (decodeList m)) with h | h | h
  · have hp : isPrefixChar m n = 1 := (isPrefixChar_eq_one_iff m n).mpr ((nbhd_subset_iff _ _).mp h)
    rw [Set.inter_eq_left.mpr h]
    constructor
    · intro heq; exact Or.inl ⟨hp, (nbhd_injective heq).symm⟩
    · rintro (⟨-, heq⟩ | ⟨hp', heq⟩)
      · rw [heq]
      · rw [isPrefixChar_eq_one_iff] at hp'
        rw [heq]
        exact Set.Subset.antisymm h ((nbhd_subset_iff (decodeList m) (decodeList n)).mpr hp')
  · have hp : isPrefixChar n m = 1 := (isPrefixChar_eq_one_iff n m).mpr ((nbhd_subset_iff _ _).mp h)
    rw [Set.inter_eq_right.mpr h]
    constructor
    · intro heq; exact Or.inr ⟨hp, (nbhd_injective heq).symm⟩
    · rintro (⟨hp', heq⟩ | ⟨-, heq⟩)
      · rw [isPrefixChar_eq_one_iff] at hp'
        rw [heq]
        exact Set.Subset.antisymm h ((nbhd_subset_iff (decodeList n) (decodeList m)).mpr hp')
      · rw [heq]
  · rw [h]
    have h1 : isPrefixChar m n ≠ 1 := by
      intro hp; rw [isPrefixChar_eq_one_iff] at hp
      obtain ⟨t, ht⟩ := (nbhd_nonempty (decodeList n))
      exact Set.notMem_empty t (h ▸ Set.mem_inter ht ((nbhd_subset_iff _ _).mpr hp ht))
    have h2 : isPrefixChar n m ≠ 1 := by
      intro hp; rw [isPrefixChar_eq_one_iff] at hp
      obtain ⟨t, ht⟩ := (nbhd_nonempty (decodeList m))
      exact Set.notMem_empty t (h ▸ Set.mem_inter ((nbhd_subset_iff _ _).mpr hp ht) ht)
    constructor
    · intro heq; exact absurd heq.symm (nbhd_nonempty (decodeList k)).ne_empty
    · rintro (⟨hp, -⟩ | ⟨hp, -⟩)
      · exact absurd hp h1
      · exact absurd hp h2
end

section
theorem Lenum_interEq_charP_eq_one_iff (n m k : ℕ) :
    Lenum n ∩ Lenum m = Lenum k ↔ LenumInterEqCharP (Nat.pair n (Nat.pair m k)) = 1 := by
  unfold LenumInterEqCharP
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [LenumInterEqChar_eq_one_iff]
  exact Lenum_interEq_iff n m k
end

section

theorem Lenum_interEq_computable : RecDecidable₃ (fun n m k => Lenum n ∩ Lenum m = Lenum k) :=
  RecDecidable₃.of_triple_zero_one_char primrec_LenumInterEqCharP
    (fun t => by have := LenumInterEqCharP_le_one t; omega)
    Lenum_interEq_charP_eq_one_iff
end

section

def Lpres : ComputablePresentation L where
  X := Lenum
  mem_X n := Lenum_mem n
  surj hY := Lenum_surj hY
  interEq_computable := Lenum_interEq_computable
  cons_computable := Lenum_cons_computable
  inter := LenumInter
  inter_primrec := primrec_LenumInter
  inter_spec h := LenumInter_spec h
  masterIdx := 0
  masterIdx_spec := Lenum_zero
end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)
variable {β γ δ : Type*}

structure LFunData {V : NeighborhoodSystem β} (P : ComputablePresentation V) where
  gN : ℕ → ℕ
  incl0 : ℕ → ℕ
  incl1 : ℕ → ℕ
  eq1 : ℕ → ℕ
  hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf Lpres P (decodeList c))
    : Set (ApproximableMap L V)).Nonempty
  hgNp : Nat.Primrec gN
  hincl0 : ∀ s, incl0 s = 1 ↔ Lpres.X s.unpair.1 ⊆ Lpres.X s.unpair.2
  hincl0p : Nat.Primrec incl0
  hincl1 : ∀ s, incl1 s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2
  hincl1p : Nat.Primrec incl1
  heq1 : ∀ s, eq1 s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2
  heq1p : Nat.Primrec eq1
end

section
instance : Nonempty Gamma := ⟨Sum.inl []⟩
end

section
@[simp] theorem cons_inl (i : ℕ) (l : List ℕ) : cons i (.inl l) = .inl (i :: l) := rfl
end

section
@[simp] theorem cons_inr (i : ℕ) (s : ℕ → ℕ) : cons i (.inr s) = .inr (streamCons i s) := rfl
end

section
@[simp] theorem L_mem {X : Set Gamma} : L.mem X ↔ Lmem X := Iff.rfl
end

section
@[simp] theorem L_master : L.master = Set.univ := rfl
end

section

def LenumSubsetChar (t : ℕ) : ℕ := isPrefixChar t.unpair.2 t.unpair.1
end

section

def finPrefix (f : ℕ → ℕ) (n : ℕ) : List ℕ := (List.range n).map f
end

section
@[simp] theorem finPrefix_zero (f : ℕ → ℕ) : finPrefix f 0 = [] := rfl
end

section

def HasMin (x : L.Element) : Prop := ∃ X, x.mem X ∧ ∀ Y, x.mem Y → X ⊆ Y
end

section

def bitToNat (b : Bool) : ℕ := if b then 1 else 0
end

section
@[simp] theorem bitToNat_false : bitToNat false = 0 := rfl
end

section
@[simp] theorem bitToNat_true : bitToNat true = 1 := rfl
end

section

def embStr (σ : ExampleB.Str) : List ℕ := σ.map bitToNat
end

section
@[simp] theorem embStr_nil : embStr [] = [] := rfl
end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

def Tenum (n : ℕ) : Set Token :=
  match n with
  | 0 => Example12.master
  | 1 => zero
  | _ => one

@[simp] theorem Tenum_zero : Tenum 0 = Example12.master := rfl

@[simp] theorem Tenum_one : Tenum 1 = zero := rfl

@[simp] theorem Tenum_two : Tenum 2 = one := rfl

theorem Tenum_eq_canon (n : ℕ) : Tenum n = Tenum (min n 2) := by
  rcases n with _ | _ | n
  · rfl
  · rfl
  · show one = Tenum (min (n + 2) 2)
    rw [show min (n + 2) 2 = 2 from by omega]
    rfl

theorem Tenum_mem (n : ℕ) : Example23.T.mem (Tenum n) := by
  rcases n with _ | _ | n
  · exact Example12.mem_master
  · exact Example12.mem_zero
  · exact Example12.mem_one

theorem Tenum_ne_empty (n : ℕ) : Tenum n ≠ (∅ : Set Token) := by
  intro h
  exact Example12.not_mem_empty (h ▸ Tenum_mem n)

theorem Tenum_surj {Y : Set Token} (hY : Example23.T.mem Y) : ∃ n, Tenum n = Y := by
  rcases (Example12.mem_iff Y).mp hY with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

def TeqChar (a b : ℕ) : ℕ := isZero ((a - b) + (b - a))

def TinterCode (a b : ℕ) : ℕ := if a = 0 then b else if b = 0 then a else if a = b then a else 3

def andCode (a b : ℕ) : ℕ := if a = 1 then b else if a = 2 then 2 else 0

noncomputable def andFn (X Y : Set Token) : Set Token :=
  if X = zero then Y else if X = one then one else Example12.master

theorem andFn_zero (Y : Set Token) : andFn zero Y = Y := by unfold andFn; rw [ite_eq_left rfl]

theorem eq_master_of_master_subset {Y : Set Token} (h : Example12.master ⊆ Y) :
    Y = Example12.master := (Set.univ_subset_iff.mp h : Y = Set.univ)

end

section

theorem exists_cons_prefix_of_prefix_of_length_lt {l l' : List ℕ} (h : l <+: l')
    (hlt : l.length < l'.length) : ∃ i, l ++ [i] <+: l' := by
  obtain ⟨r, hr⟩ := h
  cases r with
  | nil => simp [← hr] at hlt
  | cons i r' => exact ⟨i, r', by rw [← hr]; simp⟩
end

section

theorem exists_extend_of_not_hasMin {x : L.Element} (hx : ¬ HasMin x) {l : List ℕ}
    (hl : x.mem (nbhd l)) : ∃ i, x.mem (nbhd (l ++ [i])) := by
  have hex : ∃ Y, x.mem Y ∧ ¬ nbhd l ⊆ Y := by
    by_contra hc; push Not at hc; exact hx ⟨nbhd l, hl, hc⟩
  obtain ⟨Y, hYmem, hnsub⟩ := hex
  obtain ⟨l', rfl⟩ := x.sub hYmem
  rcases L_nestedOrDisjoint (mem_nbhd l) (mem_nbhd l') with hsub | hsub | hdisj
  · exact absurd hsub hnsub
  · have hpre : l <+: l' := (nbhd_subset_iff l' l).mp hsub
    have hne : l ≠ l' := by rintro rfl; exact hnsub subset_rfl
    have hlt : l.length < l'.length :=
      lt_of_le_of_ne hpre.length_le (fun heqlen => hne (hpre.eq_of_length heqlen))
    obtain ⟨i, hi⟩ := exists_cons_prefix_of_prefix_of_length_lt hpre hlt
    exact ⟨i, x.up_mem hYmem (mem_nbhd _) ((nbhd_subset_iff l' (l ++ [i])).mpr hi)⟩
  · exfalso
    have hxmem : x.mem (nbhd l ∩ nbhd l') := x.inter_mem hl hYmem
    rw [hdisj] at hxmem
    obtain ⟨l'', hl''⟩ := x.sub hxmem
    exact (nbhd_nonempty l'').ne_empty hl''.symm
end

section

noncomputable def buildData (x : L.Element) (hx : ¬ HasMin x) :
    ∀ n : ℕ, {l : List ℕ // x.mem (nbhd l) ∧ l.length = n} :=
  fun n =>
    Nat.rec (⟨[], x.master_mem, rfl⟩ : {l : List ℕ // x.mem (nbhd l) ∧ l.length = 0})
      (fun n prev =>
        ⟨prev.1 ++ [Classical.choose (exists_extend_of_not_hasMin hx prev.2.1)],
          Classical.choose_spec (exists_extend_of_not_hasMin hx prev.2.1),
          by rw [List.length_append, List.length_singleton, prev.2.2]⟩)
      n
end

section
theorem finPrefix_length (f : ℕ → ℕ) (n : ℕ) : (finPrefix f n).length = n := by
  unfold finPrefix; rw [List.length_map, List.length_range]
end

section
theorem finPrefix_succ (f : ℕ → ℕ) (n : ℕ) :
    finPrefix f (n + 1) = finPrefix f n ++ [f n] := by
  unfold finPrefix; rw [List.range_succ, List.map_append, List.map_singleton]
end

section
theorem finPrefix_prefix_succ (f : ℕ → ℕ) (n : ℕ) : finPrefix f n <+: finPrefix f (n + 1) := by
  rw [finPrefix_succ]; exact List.prefix_append _ _
end

section
theorem finPrefix_prefix_of_le (f : ℕ → ℕ) {n m : ℕ} (h : n ≤ m) :
    finPrefix f n <+: finPrefix f m := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (finPrefix_prefix_succ f _)
end

section
theorem finPrefix_take (f : ℕ → ℕ) {n m : ℕ} (h : n ≤ m) :
    (finPrefix f m).take n = finPrefix f n := by
  unfold finPrefix; rw [← List.map_take, List.take_range, min_eq_left h]
end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

theorem master_ne_one_T : Example12.master ≠ one := by
  intro h
  have h1 : (0 : Token) ∈ Example12.master := by simp [Example12.master]
  rw [h] at h1; simp [one] at h1

theorem master_ne_zero_T : Example12.master ≠ zero := by
  intro h
  have h1 : (1 : Token) ∈ Example12.master := by simp [Example12.master]
  rw [h] at h1; simp [zero] at h1

theorem andFn_master (Y : Set Token) : andFn Example12.master Y = Example12.master := by
  unfold andFn; rw [ite_eq_right master_ne_zero_T, ite_eq_right master_ne_one_T]

end

section

theorem nbhd_finPrefix_antitone (f : ℕ → ℕ) {n m : ℕ} (h : n ≤ m) :
    nbhd (finPrefix f m) ⊆ nbhd (finPrefix f n) :=
  (nbhd_subset_iff _ _).mpr (finPrefix_prefix_of_le f h)
end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

def notCode (c : ℕ) : ℕ := if c = 1 then 2 else if c = 2 then 1 else 0

noncomputable def notFn (X : Set Token) : Set Token :=
  if X = zero then one else if X = one then zero else Example12.master

theorem notFn_master : notFn Example12.master = Example12.master := by
  unfold notFn; rw [ite_eq_right master_ne_zero_T, ite_eq_right master_ne_one_T]

theorem notFn_zero : notFn zero = one := by unfold notFn; rw [ite_eq_left rfl]

end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)
variable {β γ δ : Type*}

noncomputable def LFunData.ofPresentation {V : NeighborhoodSystem β} (P : ComputablePresentation V) :
    LFunData P where
  gN := funConsChar Lpres P Lpres.cons_computable.choose P.cons_computable.choose
  incl0 := Lpres.incl_computable.choose
  incl1 := P.incl_computable.choose
  eq1 := P.eq_computable.choose
  hgN := funConsChar_spec Lpres P Lpres.cons_computable.choose P.cons_computable.choose
    (fun s => (Lpres.cons_computable.choose_spec.2 s).symm)
    (fun s => (P.cons_computable.choose_spec.2 s).symm)
  hgNp := primrec_funConsChar Lpres P Lpres.cons_computable.choose P.cons_computable.choose
    Lpres.cons_computable.choose_spec.1 P.cons_computable.choose_spec.1
  hincl0 := fun s => (Lpres.incl_computable.choose_spec.2 s).symm
  hincl0p := Lpres.incl_computable.choose_spec.1
  hincl1 := fun s => (P.incl_computable.choose_spec.2 s).symm
  hincl1p := P.incl_computable.choose_spec.1
  heq1 := fun s => (P.eq_computable.choose_spec.2 s).symm
  heq1p := P.eq_computable.choose_spec.1
end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

theorem one_inter_zero_T : one ∩ zero = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [zero, one]
end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)
variable {β γ δ : Type*}

def postcompose {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
    (h : ApproximableMap V₁ V₂) : ApproximableMap (funSpace L V₁) (funSpace L V₂) :=
  curry (h.comp (evalMap L V₁))

def LFunData.pres {V : NeighborhoodSystem β} {P : ComputablePresentation V} (d : LFunData P) :
    ComputablePresentation (funSpace L V) :=
  funPresentation Lpres P d.gN d.incl0 d.incl1 d.eq1 d.hgN d.hgNp d.hincl0 d.hincl0p
    d.hincl1 d.hincl1p d.heq1 d.heq1p

end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

theorem primrec_TeqChar {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => TeqChar (f n) (g n)) :=
  (primrec_isZero.comp (primrec_add₂ (primrec_sub₂ hf hg) (primrec_sub₂ hg hf))).of_eq
    fun _ => rfl

theorem primrec_TinterCode {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => TinterCode (f n) (g n)) := by
  have heq : Nat.Primrec (fun n => TeqChar (f n) (g n)) := primrec_TeqChar hf hg
  have hz1 := primrec_selectFn heq hf (Nat.Primrec.const 3)
  have hz2 := primrec_selectFn (primrec_isZero.comp hg) hf hz1
  refine (primrec_selectFn (primrec_isZero.comp hf) hg hz2).of_eq fun n => ?_
  unfold TinterCode TeqChar
  by_cases h0 : f n = 0
  · rw [ite_eq_left h0, h0, isZero]; simp
  · rw [ite_eq_right h0]
    have hz0 : isZero (f n) = 0 := by unfold isZero; omega
    rw [hz0, selectFn_zero]
    by_cases h1 : g n = 0
    · rw [ite_eq_left h1, h1, isZero]; simp
    · rw [ite_eq_right h1]
      have hz0' : isZero (g n) = 0 := by unfold isZero; omega
      rw [hz0', selectFn_zero]
      by_cases h2 : f n = g n
      · have : isZero ((f n - g n) + (g n - f n)) = 1 := by unfold isZero; omega
        rw [ite_eq_left h2, this, selectFn_one]
      · have : isZero ((f n - g n) + (g n - f n)) = 0 := by unfold isZero; omega
        rw [ite_eq_right h2, this, selectFn_zero]

end

section
theorem principal_hasMin (l : List ℕ) : HasMin (L.principal (mem_nbhd l)) :=
  ⟨nbhd l, ⟨mem_nbhd l, subset_rfl⟩, fun _ hY => hY.2⟩
end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)
variable {β γ δ : Type*}

def pwArg (V₀ : NeighborhoodSystem β) (V₁ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace L V₀) (funSpace L V₁)) L) L :=
  proj₁ (prod (funSpace L V₀) (funSpace L V₁)) L

def pwFst (V₀ : NeighborhoodSystem β) (V₁ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace L V₀) (funSpace L V₁)) L) (funSpace L V₀) :=
  (proj₀ (funSpace L V₀) (funSpace L V₁)).comp (proj₀ (prod (funSpace L V₀) (funSpace L V₁)) L)

def pwSnd (V₀ : NeighborhoodSystem β) (V₁ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace L V₀) (funSpace L V₁)) L) (funSpace L V₁) :=
  (proj₁ (funSpace L V₀) (funSpace L V₁)).comp (proj₀ (prod (funSpace L V₀) (funSpace L V₁)) L)

def pointwiseBin {V₀ : NeighborhoodSystem β} {V₁ : NeighborhoodSystem γ} {V₂ : NeighborhoodSystem δ}
    (h : ApproximableMap (prod V₀ V₁) V₂) :
    ApproximableMap (prod (funSpace L V₀) (funSpace L V₁)) (funSpace L V₂) :=
  curry (h.comp (paired
    ((evalMap L V₀).comp (paired (pwFst V₀ V₁) (pwArg V₀ V₁)))
    ((evalMap L V₁).comp (paired (pwSnd V₀ V₁) (pwArg V₀ V₁)))))

end

section

def streamElement (f : ℕ → ℕ) : L.Element where
  mem Z := L.mem Z ∧ ∃ n, nbhd (finPrefix f n) ⊆ Z
  sub h := h.1
  master_mem := ⟨mem_nbhd [], 0, subset_rfl⟩
  inter_mem := by
    rintro X Y ⟨hXmem, n, hXsub⟩ ⟨hYmem, m, hYsub⟩
    have hn : nbhd (finPrefix f (max n m)) ⊆ X :=
      (nbhd_finPrefix_antitone f (le_max_left n m)).trans hXsub
    have hm : nbhd (finPrefix f (max n m)) ⊆ Y :=
      (nbhd_finPrefix_antitone f (le_max_right n m)).trans hYsub
    exact ⟨L.inter_mem hXmem hYmem (mem_nbhd _) (Set.subset_inter hn hm),
      max n m, Set.subset_inter hn hm⟩
  up_mem := by
    rintro X Y ⟨-, n, hn⟩ hYmem hXY
    exact ⟨hYmem, n, hn.trans hXY⟩
end

section

theorem finPrefix_eq_of_streamElement_eq {f₁ f₂ : ℕ → ℕ} (heq : streamElement f₁ = streamElement f₂) :
    ∀ n, finPrefix f₁ n = finPrefix f₂ n := by
  intro n
  have hmem1 : (streamElement f₁).mem (nbhd (finPrefix f₁ n)) := ⟨mem_nbhd _, n, subset_rfl⟩
  rw [heq] at hmem1
  obtain ⟨-, m, hm⟩ := hmem1
  have hpre : finPrefix f₁ n <+: finPrefix f₂ m := (nbhd_subset_iff _ _).mp hm
  have hlen : n ≤ m := by
    have hl := hpre.length_le; rwa [finPrefix_length, finPrefix_length] at hl
  have hpre' : finPrefix f₁ n = (finPrefix f₂ m).take (finPrefix f₁ n).length :=
    List.prefix_iff_eq_take.mp hpre
  rw [finPrefix_length] at hpre'
  rw [hpre', finPrefix_take f₂ hlen]
end

section

theorem streamElement_injective : Function.Injective streamElement := by
  intro f₁ f₂ heq
  have hpre := finPrefix_eq_of_streamElement_eq heq
  funext n
  have h1 := hpre (n + 1)
  rw [finPrefix_succ, finPrefix_succ, hpre n] at h1
  simpa using List.append_cancel_left h1
end

section

theorem streamElement_not_hasMin (f : ℕ → ℕ) : ¬ HasMin (streamElement f) := by
  rintro ⟨X, ⟨-, n, hXsub⟩, hmin⟩
  have hmemsucc : (streamElement f).mem (nbhd (finPrefix f (n + 1))) := ⟨mem_nbhd _, n + 1, subset_rfl⟩
  have hle : X ⊆ nbhd (finPrefix f (n + 1)) := hmin _ hmemsucc
  have heq : nbhd (finPrefix f n) = nbhd (finPrefix f (n + 1)) :=
    Set.Subset.antisymm (hXsub.trans hle) (nbhd_finPrefix_antitone f (Nat.le_succ n))
  have hlen := congrArg List.length (nbhd_injective heq)
  rw [finPrefix_length, finPrefix_length] at hlen
  omega
end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

theorem subset_iff_eq_or_eq_master {X' X : Set Token} (hX' : Example23.T.mem X')
    (hX : Example23.T.mem X) (h : X' ⊆ X) : X' = X ∨ X = Example12.master := by
  rcases (Example12.mem_iff X).mp hX with rfl | rfl | rfl
  · exact Or.inr rfl
  · refine Or.inl ?_
    rcases (Example12.mem_iff X').mp hX' with rfl | rfl | rfl
    · exact absurd (show (1 : Token) ∈ zero from h (by simp [Example12.master])) (by simp [zero])
    · rfl
    · exact absurd (show (1 : Token) ∈ zero from h (by simp [one])) (by simp [zero])
  · refine Or.inl ?_
    rcases (Example12.mem_iff X').mp hX' with rfl | rfl | rfl
    · exact absurd (show (0 : Token) ∈ one from h (by simp [Example12.master])) (by simp [one])
    · exact absurd (show (0 : Token) ∈ one from h (by simp [zero])) (by simp [one])
    · rfl
end

section

def toElement : Gamma → L.Element
  | .inl l => L.principal (L_mem.mpr (mem_nbhd l))
  | .inr f => streamElement f
end

section

theorem toElement_injective : Function.Injective toElement := by
  rintro (l₁ | f₁) (l₂ | f₂) heq
  · exact congrArg Sum.inl
      (nbhd_injective (principal_injective (V := L) (mem_nbhd l₁) (mem_nbhd l₂) heq))
  · have heq' : L.principal (mem_nbhd l₁) = streamElement f₂ := heq
    exact absurd (heq' ▸ principal_hasMin l₁) (streamElement_not_hasMin f₂)
  · have heq' : streamElement f₁ = L.principal (mem_nbhd l₂) := heq
    exact absurd (principal_hasMin l₂) (heq' ▸ streamElement_not_hasMin f₁)
  · exact congrArg Sum.inr (streamElement_injective heq)
end

section

noncomputable def toStream (x : L.Element) (hx : ¬ HasMin x) (n : ℕ) : ℕ :=
  Classical.choose (exists_extend_of_not_hasMin hx (buildData x hx n).2.1)
end

section
theorem buildData_succ (x : L.Element) (hx : ¬ HasMin x) (n : ℕ) :
    (buildData x hx (n + 1)).1 = (buildData x hx n).1 ++ [toStream x hx n] := rfl
end

section
theorem buildData_eq_finPrefix (x : L.Element) (hx : ¬ HasMin x) :
    ∀ n, (buildData x hx n).1 = finPrefix (toStream x hx) n
  | 0 => rfl
  | n + 1 => by rw [buildData_succ, finPrefix_succ, buildData_eq_finPrefix x hx n]
end

section
theorem mem_nbhd_finPrefix_toStream (x : L.Element) (hx : ¬ HasMin x) (n : ℕ) :
    x.mem (nbhd (finPrefix (toStream x hx) n)) :=
  buildData_eq_finPrefix x hx n ▸ (buildData x hx n).2.1
end

section

theorem exists_finPrefix_subset_of_mem (x : L.Element) (hx : ¬ HasMin x) {Z : Set Gamma}
    (hZ : x.mem Z) : ∃ n, nbhd (finPrefix (toStream x hx) n) ⊆ Z := by
  obtain ⟨l, rfl⟩ := x.sub hZ
  refine ⟨l.length + 1, ?_⟩
  set n := l.length + 1
  have hn : x.mem (nbhd (finPrefix (toStream x hx) n)) := mem_nbhd_finPrefix_toStream x hx n
  have hinter := x.inter_mem hZ hn
  rcases L_nestedOrDisjoint (mem_nbhd l) (mem_nbhd (finPrefix (toStream x hx) n)) with
    hsub | hsub | hdisj
  ·
    have hpre : finPrefix (toStream x hx) n <+: l := (nbhd_subset_iff l _).mp hsub
    have := hpre.length_le
    rw [finPrefix_length] at this
    omega
  · exact hsub
  · exfalso
    rw [hdisj] at hinter
    obtain ⟨l', hl'⟩ := x.sub hinter
    exact (nbhd_nonempty l').ne_empty hl'.symm
end

section

theorem toElement_surjective : Function.Surjective toElement := by
  intro x
  by_cases hx : HasMin x
  · obtain ⟨X, hXmem, hXmin⟩ := hx
    obtain ⟨l, rfl⟩ := x.sub hXmem
    exact ⟨Sum.inl l, (eq_principal_of_isMin (V := L) x hXmem hXmin).symm⟩
  · exact ⟨Sum.inr (toStream x hx), by
      apply Element.ext
      intro Z
      constructor
      · rintro ⟨hZmem, n, hn⟩
        exact x.up_mem (mem_nbhd_finPrefix_toStream x hx n) hZmem hn
      · intro hZ
        exact ⟨x.sub hZ, exists_finPrefix_subset_of_mem x hx hZ⟩⟩
end

section

theorem toElement_bijective : Function.Bijective toElement :=
  ⟨toElement_injective, toElement_surjective⟩
end

section

noncomputable def gammaEquivElement : Gamma ≃ L.Element :=
  Equiv.ofBijective toElement toElement_bijective
end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

theorem zero_inter_one_T : zero ∩ one = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [zero, one]

theorem Tenum_inter_eq {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) :
    Tenum a ∩ Tenum b = if a = 0 then Tenum b else if b = 0 then Tenum a
      else if a = b then Tenum a else (∅ : Set Token) := by
  interval_cases a <;> interval_cases b <;>
    simp [Tenum, Example12.master, Set.univ_inter, Set.inter_univ, Set.inter_self,
      zero_inter_one_T, one_inter_zero_T]

theorem Tenum_inter_eq_TinterCode' {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) :
    Tenum a ∩ Tenum b = if TinterCode a b = 3 then (∅ : Set Token) else Tenum (TinterCode a b) := by
  interval_cases a <;> interval_cases b <;>
    simp [Tenum, TinterCode, Example12.master, Set.univ_inter, Set.inter_univ, Set.inter_self,
      zero_inter_one_T, one_inter_zero_T]

theorem Tenum_inter_eq_TinterCode (n m : ℕ) :
    Tenum n ∩ Tenum m = if TinterCode (min n 2) (min m 2) = 3 then (∅ : Set Token)
      else Tenum (TinterCode (min n 2) (min m 2)) := by
  rw [Tenum_eq_canon n, Tenum_eq_canon m]
  exact Tenum_inter_eq_TinterCode' (Nat.min_le_right n 2) (Nat.min_le_right m 2)

theorem Tpres_cons_iff (n m : ℕ) :
    (∃ k, Tenum k ⊆ Tenum n ∩ Tenum m) ↔ TinterCode (min n 2) (min m 2) ≠ 3 := by
  rw [Tenum_inter_eq_TinterCode n m]
  constructor
  · rintro ⟨k, hk⟩ hcontra
    rw [ite_eq_left hcontra] at hk
    exact Tenum_ne_empty k (Set.subset_empty_iff.mp hk)
  · intro hne
    rw [ite_eq_right hne]
    exact ⟨TinterCode (min n 2) (min m 2), subset_rfl⟩

theorem Tpres_cons_computable : RecDecidable₂ (fun n m => ∃ k, Tenum k ⊆ Tenum n ∩ Tenum m) := by
  have ha : Nat.Primrec (fun t : ℕ => TinterCode (min t.unpair.1 2) (min t.unpair.2 2)) :=
    primrec_TinterCode (primrec_min Nat.Primrec.left (Nat.Primrec.const 2))
      (primrec_min Nat.Primrec.right (Nat.Primrec.const 2))
  have hne : RecDecidable (fun t : ℕ => TinterCode (min t.unpair.1 2) (min t.unpair.2 2) ≠ 3) :=
    (RecDecidable.natEq ha (Nat.Primrec.const 3)).not
  exact RecDecidable.of_iff (fun t => Tpres_cons_iff t.unpair.1 t.unpair.2) hne

theorem zero_ne_one_T : zero ≠ one := by
  intro h
  have h1 : (0 : Token) ∈ zero := by simp [zero]
  rw [h] at h1; simp [one] at h1

theorem Tenum_injOn {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) (h : Tenum a = Tenum b) : a = b := by
  interval_cases a <;> interval_cases b <;>
    simp only [Tenum_zero, Tenum_one, Tenum_two] at h <;>
    first
      | rfl
      | exact absurd h master_ne_zero_T
      | exact absurd h.symm master_ne_zero_T
      | exact absurd h master_ne_one_T
      | exact absurd h.symm master_ne_one_T
      | exact absurd h zero_ne_one_T
      | exact absurd h.symm zero_ne_one_T

theorem Tenum_interEq_iff {a b c : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2) :
    Tenum a ∩ Tenum b = Tenum c ↔ TinterCode a b = c := by
  rw [Tenum_inter_eq ha hb]
  unfold TinterCode
  split_ifs with h1 h2 h3
  · exact ⟨fun h => (Tenum_injOn hb hc h).symm ▸ rfl, fun h => h ▸ rfl⟩
  · exact ⟨fun h => (Tenum_injOn ha hc h).symm ▸ rfl, fun h => h ▸ rfl⟩
  · exact ⟨fun h => (Tenum_injOn ha hc h).symm ▸ rfl, fun h => h ▸ rfl⟩
  · exact ⟨fun h => absurd h.symm (Tenum_ne_empty c), fun h => absurd h.symm (by omega)⟩

theorem Tenum_interEq_iff' (n m k : ℕ) :
    Tenum n ∩ Tenum m = Tenum k ↔ TinterCode (min n 2) (min m 2) = min k 2 := by
  rw [Tenum_eq_canon n, Tenum_eq_canon m, Tenum_eq_canon k,
    Tenum_interEq_iff (Nat.min_le_right n 2) (Nat.min_le_right m 2) (Nat.min_le_right k 2)]

theorem Tpres_interEq_computable : RecDecidable₃ (fun n m k => Tenum n ∩ Tenum m = Tenum k) := by
  have ha : Nat.Primrec (fun t : ℕ => TinterCode (min t.unpair.1 2) (min t.unpair.2.unpair.1 2)) :=
    primrec_TinterCode (primrec_min Nat.Primrec.left (Nat.Primrec.const 2))
      (primrec_min (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 2))
  have hb : Nat.Primrec (fun t : ℕ => min t.unpair.2.unpair.2 2) :=
    primrec_min (Nat.Primrec.right.comp Nat.Primrec.right) (Nat.Primrec.const 2)
  exact RecDecidable.of_iff
    (fun t => Tenum_interEq_iff' t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)
    (RecDecidable.natEq ha hb)

def Tpres : ComputablePresentation Example23.T where
  X := Tenum
  mem_X := Tenum_mem
  surj := Tenum_surj
  interEq_computable := Tpres_interEq_computable
  cons_computable := Tpres_cons_computable
  inter n m := TinterCode (min n 2) (min m 2)
  inter_primrec :=
    (primrec_TinterCode (primrec_min Nat.Primrec.left (Nat.Primrec.const 2))
      (primrec_min Nat.Primrec.right (Nat.Primrec.const 2))).of_eq fun _ => rfl
  inter_spec {n m} h := by
    rw [Tenum_inter_eq_TinterCode n m, ite_eq_right ((Tpres_cons_iff n m).mp h)]
  masterIdx := 0
  masterIdx_spec := rfl

end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)
variable {β γ δ : Type*}

noncomputable def LTdata : LFunData Tpres := LFunData.ofPresentation Tpres

noncomputable def LTpres : ComputablePresentation (funSpace L Example23.T) := LTdata.pres

end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

theorem andFn_one (Y : Set Token) : andFn one Y = one := by
  unfold andFn; rw [ite_eq_right (Ne.symm zero_ne_one_T), ite_eq_left rfl]

theorem andFn_mem {X Y : Set Token} (hX : Example23.T.mem X) (hY : Example23.T.mem Y) :
    Example23.T.mem (andFn X Y) := by
  rcases (Example12.mem_iff X).mp hX with rfl | rfl | rfl
  · rw [andFn_master]; exact Example12.mem_master
  · rw [andFn_zero]; exact hY
  · rw [andFn_one]; exact Example12.mem_one

noncomputable def andMap2 : ApproximableMap₂ Example23.T Example23.T Example23.T where
  rel X Y Z := Example23.T.mem X ∧ Example23.T.mem Y ∧ Example23.T.mem Z ∧ andFn X Y ⊆ Z
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨Example12.mem_master, Example12.mem_master, Example12.mem_master, by
    show andFn Example12.master Example12.master ⊆ Example12.master
    rw [andFn_master]⟩
  inter_right := by
    rintro X Y Z Z' ⟨hX, hY, hZ, hsub⟩ ⟨_, _, hZ', hsub'⟩
    exact ⟨hX, hY, Example23.T.inter_mem hZ hZ' (andFn_mem hX hY) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨hX, hY, hZ, hsub⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    refine ⟨hX', hY', hZ', ?_⟩
    rcases (Example12.mem_iff X).mp hX with rfl | rfl | rfl
    · rw [andFn_master] at hsub
      have hZ'master : Z' = Example12.master := eq_master_of_master_subset (hsub.trans hZZ')
      rw [hZ'master, Example12.master]; exact Set.subset_univ _
    · rw [andFn_zero] at hsub
      have hX'eq : X' = zero :=
        (subset_iff_eq_or_eq_master hX' Example12.mem_zero hX'X).resolve_right
          master_ne_zero_T.symm
      rw [hX'eq, andFn_zero]
      exact (hY'Y.trans hsub).trans hZZ'
    · rw [andFn_one] at hsub
      have hX'eq : X' = one :=
        (subset_iff_eq_or_eq_master hX' Example12.mem_one hX'X).resolve_right
          master_ne_one_T.symm
      rw [hX'eq, andFn_one]
      exact hsub.trans hZZ'

noncomputable def andT : ApproximableMap (prod Example23.T Example23.T) Example23.T :=
  ofMap₂ andMap2

theorem notFn_one : notFn one = zero := by
  unfold notFn; rw [ite_eq_right (Ne.symm zero_ne_one_T), ite_eq_left rfl]

theorem notFn_mem {X : Set Token} (hX : Example23.T.mem X) : Example23.T.mem (notFn X) := by
  rcases (Example12.mem_iff X).mp hX with rfl | rfl | rfl
  · rw [notFn_master]; exact Example12.mem_master
  · rw [notFn_zero]; exact Example12.mem_one
  · rw [notFn_one]; exact Example12.mem_zero

noncomputable def notT : ApproximableMap Example23.T Example23.T where
  rel X Y := Example23.T.mem X ∧ Example23.T.mem Y ∧ notFn X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨Example12.mem_master, Example12.mem_master, by
    show notFn Example12.master ⊆ Example12.master; rw [notFn_master]⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    exact ⟨hX, Example23.T.inter_mem hY hY' (notFn_mem hX) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hsub⟩ hX'X hYY' hX' hY'
    refine ⟨hX', hY', ?_⟩
    rcases subset_iff_eq_or_eq_master hX' hX hX'X with heq | heq
    · rw [heq]; exact hsub.trans hYY'
    · rw [heq, notFn_master] at hsub
      have hY'master : Y' = Example12.master := eq_master_of_master_subset (hsub.trans hYY')
      rw [hY'master, Example12.master]; exact Set.subset_univ _

end

section
theorem bitToNat_injective : Function.Injective bitToNat := by
  intro a b h; cases a <;> cases b <;> simp_all [bitToNat]

theorem embStr_cons (b : Bool) (s : ExampleB.Str) : embStr (b :: s) = bitToNat b :: embStr s := rfl

theorem embStr_prefix_iff : ∀ σ τ : ExampleB.Str, embStr σ <+: embStr τ ↔ σ <+: τ := by
  intro σ
  induction σ with
  | nil => intro τ; simp
  | cons b s ih =>
    intro τ
    cases τ with
    | nil => simp [embStr_cons]
    | cons c t =>
      rw [embStr_cons, embStr_cons, List.cons_prefix_cons, List.cons_prefix_cons,
        bitToNat_injective.eq_iff, ih t]

theorem cone_subset_cone_iff_nbhd_embStr (σ τ : ExampleB.Str) :
    ExampleB.cone σ ⊆ ExampleB.cone τ ↔ nbhd (embStr σ) ⊆ nbhd (embStr τ) := by
  rw [ExampleB.cone_subset_cone, nbhd_subset_iff, embStr_prefix_iff]

theorem sigmaBot_le_iff_toElement_inl_embStr (σ τ : ExampleB.Str) :
    ExampleB.sigmaBot σ ≤ ExampleB.sigmaBot τ ↔
      toElement (Sum.inl (embStr σ)) ≤ toElement (Sum.inl (embStr τ)) := by
  show ExampleB.sigmaBot σ ≤ ExampleB.sigmaBot τ ↔
      L.principal (L_mem.mpr (mem_nbhd (embStr σ))) ≤
        L.principal (L_mem.mpr (mem_nbhd (embStr τ)))
  rw [ExampleB.sigmaBot_le_iff, L.principal_le_iff, nbhd_subset_iff, embStr_prefix_iff]

open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

theorem primrec_notCode {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec (fun n => notCode (f n)) := by
  refine (primrec_selectFn (primrec_TeqChar hf (Nat.Primrec.const 1)) (Nat.Primrec.const 2)
    (primrec_selectFn (primrec_TeqChar hf (Nat.Primrec.const 2)) (Nat.Primrec.const 1)
      (Nat.Primrec.const 0))).of_eq fun n => ?_
  unfold notCode
  by_cases h1 : f n = 1
  · have h1' : TeqChar (f n) 1 = 1 := by unfold TeqChar isZero; omega
    rw [ite_eq_left h1, h1', selectFn_one]
  · have h1' : TeqChar (f n) 1 = 0 := by unfold TeqChar isZero; omega
    rw [ite_eq_right h1, h1', selectFn_zero]
    by_cases h2 : f n = 2
    · have h2' : TeqChar (f n) 2 = 1 := by unfold TeqChar isZero; omega
      rw [ite_eq_left h2, h2', selectFn_one]
    · have h2' : TeqChar (f n) 2 = 0 := by unfold TeqChar isZero; omega
      rw [ite_eq_right h2, h2', selectFn_zero]

theorem notFn_Tenum (n : ℕ) : notFn (Tenum n) = Tenum (notCode (min n 2)) := by
  rw [Tenum_eq_canon n]
  have hc2 : min n 2 ≤ 2 := Nat.min_le_right n 2
  interval_cases (min n 2) <;> simp [Tenum, notCode, notFn_master, notFn_zero, notFn_one]

theorem notT_isComputable : ComputableMap Tpres Tpres notT := by
  constructor
  have hcomp : Nat.Primrec (fun t : ℕ => Nat.pair (notCode (min t.unpair.1 2)) t.unpair.2) :=
    (primrec_notCode (primrec_min Nat.Primrec.left (Nat.Primrec.const 2))).pair Nat.Primrec.right
  have hdec : RecDecidable₂ (fun n m => Tenum (notCode (min n 2)) ⊆ Tenum m) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd]; rfl)
      (Tpres.incl_computable.comp hcomp)
  have hiff : ∀ n m, notT.rel (Tenum n) (Tenum m) ↔ Tenum (notCode (min n 2)) ⊆ Tenum m := by
    intro n m
    show (Example23.T.mem (Tenum n) ∧ Example23.T.mem (Tenum m) ∧ notFn (Tenum n) ⊆ Tenum m) ↔ _
    rw [notFn_Tenum]
    exact ⟨fun h => h.2.2, fun h => ⟨Tenum_mem n, Tenum_mem m, h⟩⟩
  have key : RecDecidable₂ (fun n m => notT.rel (Tenum n) (Tenum m)) :=
    RecDecidable.of_iff (fun t => hiff t.unpair.1 t.unpair.2) hdec
  exact key.re

theorem primrec_andCode {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => andCode (f n) (g n)) := by
  refine (primrec_selectFn (primrec_TeqChar hf (Nat.Primrec.const 1)) hg
    (primrec_selectFn (primrec_TeqChar hf (Nat.Primrec.const 2)) (Nat.Primrec.const 2)
      (Nat.Primrec.const 0))).of_eq fun n => ?_
  unfold andCode
  by_cases h1 : f n = 1
  · have h1' : TeqChar (f n) 1 = 1 := by unfold TeqChar isZero; omega
    rw [ite_eq_left h1, h1', selectFn_one]
  · have h1' : TeqChar (f n) 1 = 0 := by unfold TeqChar isZero; omega
    rw [ite_eq_right h1, h1', selectFn_zero]
    by_cases h2 : f n = 2
    · have h2' : TeqChar (f n) 2 = 1 := by unfold TeqChar isZero; omega
      rw [ite_eq_left h2, h2', selectFn_one]
    · have h2' : TeqChar (f n) 2 = 0 := by unfold TeqChar isZero; omega
      rw [ite_eq_right h2, h2', selectFn_zero]

theorem andFn_Tenum (n m : ℕ) :
    andFn (Tenum n) (Tenum m) = Tenum (andCode (min n 2) (min m 2)) := by
  rw [Tenum_eq_canon n, Tenum_eq_canon m]
  have hn2 : min n 2 ≤ 2 := Nat.min_le_right n 2
  have hm2 : min m 2 ≤ 2 := Nat.min_le_right m 2
  interval_cases (min n 2) <;> interval_cases (min m 2) <;>
    simp [Tenum, andCode, andFn_master, andFn_zero, andFn_one]

theorem andT_isComputable : ComputableMap (prodPresentation Tpres Tpres) Tpres andT := by
  constructor
  have hcomp : Nat.Primrec (fun s : ℕ => Nat.pair
      (andCode (min s.unpair.1.unpair.1 2) (min s.unpair.1.unpair.2 2)) s.unpair.2) :=
    (primrec_andCode (primrec_min (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 2))
      (primrec_min (Nat.Primrec.right.comp Nat.Primrec.left) (Nat.Primrec.const 2))).pair
      Nat.Primrec.right
  have hdec : RecDecidable₂
      (fun t k => Tenum (andCode (min t.unpair.1 2) (min t.unpair.2 2)) ⊆ Tenum k) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd]; rfl)
      (Tpres.incl_computable.comp hcomp)
  have hiff : ∀ n m k, andT.rel (prodNbhd (Tenum n) (Tenum m)) (Tenum k) ↔
      Tenum (andCode (min n 2) (min m 2)) ⊆ Tenum k := by
    intro n m k
    have hstep : andT.rel (prodNbhd (Tenum n) (Tenum m)) (Tenum k) ↔
        andMap2.rel (Tenum n) (Tenum m) (Tenum k) := by
      show ((prod Example23.T Example23.T).mem (prodNbhd (Tenum n) (Tenum m)) ∧
        andMap2.rel (Sum.inl ⁻¹' prodNbhd (Tenum n) (Tenum m))
          (Sum.inr ⁻¹' prodNbhd (Tenum n) (Tenum m)) (Tenum k)) ↔ _
      rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
      exact and_iff_right (prod_mem_prodNbhd (Tenum_mem n) (Tenum_mem m))
    rw [hstep]
    show (Example23.T.mem (Tenum n) ∧ Example23.T.mem (Tenum m) ∧ Example23.T.mem (Tenum k) ∧
      andFn (Tenum n) (Tenum m) ⊆ Tenum k) ↔ _
    rw [andFn_Tenum n m]
    exact ⟨fun h => h.2.2.2, fun h => ⟨Tenum_mem n, Tenum_mem m, Tenum_mem k, h⟩⟩
  have key : RecDecidable₂
      (fun t k => andT.rel ((prodPresentation Tpres Tpres).X t) (Tpres.X k)) :=
    RecDecidable.of_iff (fun s => by
      show andT.rel ((prodPresentation Tpres Tpres).X s.unpair.1) (Tpres.X s.unpair.2) ↔ _
      rw [prodPresentation_X]
      exact hiff s.unpair.1.unpair.1 s.unpair.1.unpair.2 s.unpair.2) hdec
  exact key.re

variable {β γ δ : Type*}

theorem postcompose_isComputable {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
    {P₁ : ComputablePresentation V₁} {P₂ : ComputablePresentation V₂}
    (d₁ : LFunData P₁) (d₂ : LFunData P₂) {h : ApproximableMap V₁ V₂}
    (hh : ComputableMap P₁ P₂ h) :
    ComputableMap d₁.pres d₂.pres (postcompose h) := by
  have heval : ComputableMap (prodPresentation d₁.pres Lpres) P₁ (evalMap L V₁) :=
    evalMap_isComputable Lpres P₁ d₁.gN d₁.incl0 d₁.incl1 d₁.eq1
      d₁.hgN d₁.hgNp d₁.hincl0 d₁.hincl0p d₁.hincl1 d₁.hincl1p d₁.heq1 d₁.heq1p
  exact curry_isComputable d₁.pres Lpres P₂ d₂.gN d₂.incl0 d₂.incl1 d₂.eq1
    d₂.hgN d₂.hgNp d₂.hincl0 d₂.hincl0p d₂.hincl1 d₂.hincl1p d₂.heq1 d₂.heq1p
    (comp_isComputable heval hh)

theorem pointwiseBin_isComputable {V₀ : NeighborhoodSystem β} {V₁ : NeighborhoodSystem γ}
    {V₂ : NeighborhoodSystem δ} {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}
    {P₂ : ComputablePresentation V₂} (d₀ : LFunData P₀) (d₁ : LFunData P₁) (d₂ : LFunData P₂)
    {h : ApproximableMap (prod V₀ V₁) V₂} (hh : ComputableMap (prodPresentation P₀ P₁) P₂ h) :
    ComputableMap (prodPresentation d₀.pres d₁.pres) d₂.pres (pointwiseBin h) := by
  have hπAB : ComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres)
      (prodPresentation d₀.pres d₁.pres) (proj₀ (prod (funSpace L V₀) (funSpace L V₁)) L) :=
    proj₀_isComputable (prodPresentation d₀.pres d₁.pres) Lpres
  have hπL : ComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) Lpres
      (proj₁ (prod (funSpace L V₀) (funSpace L V₁)) L) :=
    proj₁_isComputable (prodPresentation d₀.pres d₁.pres) Lpres
  have hp0 : ComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) d₀.pres
      (pwFst V₀ V₁) := comp_isComputable hπAB (proj₀_isComputable d₀.pres d₁.pres)
  have hp1 : ComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) d₁.pres
      (pwSnd V₀ V₁) := comp_isComputable hπAB (proj₁_isComputable d₀.pres d₁.pres)
  have heval0 : ComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) P₀
      ((evalMap L V₀).comp (paired (pwFst V₀ V₁) (pwArg V₀ V₁))) :=
    comp_isComputable (paired_isComputable hp0 hπL)
      (evalMap_isComputable Lpres P₀ d₀.gN d₀.incl0 d₀.incl1 d₀.eq1
        d₀.hgN d₀.hgNp d₀.hincl0 d₀.hincl0p d₀.hincl1 d₀.hincl1p d₀.heq1 d₀.heq1p)
  have heval1 : ComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) P₁
      ((evalMap L V₁).comp (paired (pwSnd V₀ V₁) (pwArg V₀ V₁))) :=
    comp_isComputable (paired_isComputable hp1 hπL)
      (evalMap_isComputable Lpres P₁ d₁.gN d₁.incl0 d₁.incl1 d₁.eq1
        d₁.hgN d₁.hgNp d₁.hincl0 d₁.hincl0p d₁.hincl1 d₁.hincl1p d₁.heq1 d₁.heq1p)
  exact curry_isComputable (prodPresentation d₀.pres d₁.pres) Lpres P₂ d₂.gN d₂.incl0 d₂.incl1
    d₂.eq1 d₂.hgN d₂.hgNp d₂.hincl0 d₂.hincl0p d₂.hincl1 d₂.hincl1p d₂.heq1 d₂.heq1p
    (comp_isComputable (paired_isComputable heval0 heval1) hh)

theorem notT_lifted_isComputable : ComputableMap LTpres LTpres (postcompose notT) :=
  postcompose_isComputable LTdata LTdata notT_isComputable

theorem andT_lifted_isComputable :
    ComputableMap (prodPresentation LTpres LTpres) LTpres (pointwiseBin andT) :=
  pointwiseBin_isComputable LTdata LTdata LTdata andT_isComputable

theorem deMorganT_isComputable :
    ComputableMap (prodPresentation LTpres LTpres) LTpres
      ((postcompose notT).comp (pointwiseBin andT)
        |>.comp (paired
          (postcompose notT |>.comp (proj₀ (funSpace L Example23.T) (funSpace L Example23.T)))
          (postcompose notT |>.comp (proj₁ (funSpace L Example23.T) (funSpace L Example23.T))))) :=
  comp_isComputable
    (paired_isComputable
      (comp_isComputable (proj₀_isComputable LTpres LTpres) notT_lifted_isComputable)
      (comp_isComputable (proj₁_isComputable LTpres LTpres) notT_lifted_isComputable))
    (comp_isComputable andT_lifted_isComputable notT_lifted_isComputable)
end

section

theorem Gamma_cases (γ : Gamma) : γ = star ∨ ∃ i γ', γ = cons i γ' := by
  cases γ with
  | inl l =>
    cases l with
    | nil => exact Or.inl rfl
    | cons i l' => exact Or.inr ⟨i, .inl l', rfl⟩
  | inr s =>
    refine Or.inr ⟨s 0, .inr (fun n => s (n + 1)), ?_⟩
    simp only [cons]
    congr 1
    funext n
    cases n <;> rfl
end

section

theorem L_isEffectivelyGiven : L.IsEffectivelyGiven := ⟨Lpres⟩
end

section
set_option linter.unusedVariables false

theorem example_724 : And
  (And
    (And
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
        DomainTheory.NeighbourhoodSystems.Exercise724.Gamma DomainTheory.NeighbourhoodSystems.Exercise724.L)
      (@DomainTheory.NeighbourhoodSystems.ComputableMap
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
        (@DomainTheory.NeighbourhoodSystems.Exercise724.postcompose DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example23.T
          DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.notT)))
    (@DomainTheory.NeighbourhoodSystems.ComputableMap
      (Sum
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
        DomainTheory.NeighbourhoodSystems.Example23.T)
      (@DomainTheory.NeighbourhoodSystems.prod
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T))
      (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
        DomainTheory.NeighbourhoodSystems.Example23.T)
      (@DomainTheory.NeighbourhoodSystems.prodPresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres)
      DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
      (@DomainTheory.NeighbourhoodSystems.Exercise724.pointwiseBin DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Example23.T
        DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.andT)))
  (@Function.Bijective DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
      DomainTheory.NeighbourhoodSystems.Exercise724.L)
    DomainTheory.NeighbourhoodSystems.Exercise724.toElement) :=
  @And.intro
  (And
    (And
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
        DomainTheory.NeighbourhoodSystems.Exercise724.Gamma DomainTheory.NeighbourhoodSystems.Exercise724.L)
      (@DomainTheory.NeighbourhoodSystems.ComputableMap
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
        (@DomainTheory.NeighbourhoodSystems.Exercise724.postcompose DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example23.T
          DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.notT)))
    (@DomainTheory.NeighbourhoodSystems.ComputableMap
      (Sum
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
        DomainTheory.NeighbourhoodSystems.Example23.T)
      (@DomainTheory.NeighbourhoodSystems.prod
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T))
      (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
        DomainTheory.NeighbourhoodSystems.Example23.T)
      (@DomainTheory.NeighbourhoodSystems.prodPresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres)
      DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
      (@DomainTheory.NeighbourhoodSystems.Exercise724.pointwiseBin DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Example23.T
        DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.andT)))
  (@Function.Bijective DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
      DomainTheory.NeighbourhoodSystems.Exercise724.L)
    DomainTheory.NeighbourhoodSystems.Exercise724.toElement)
  (@And.intro
    (And
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
        DomainTheory.NeighbourhoodSystems.Exercise724.Gamma DomainTheory.NeighbourhoodSystems.Exercise724.L)
      (@DomainTheory.NeighbourhoodSystems.ComputableMap
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
        (@DomainTheory.NeighbourhoodSystems.Exercise724.postcompose DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example23.T
          DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.notT)))
    (@DomainTheory.NeighbourhoodSystems.ComputableMap
      (Sum
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
        DomainTheory.NeighbourhoodSystems.Example23.T)
      (@DomainTheory.NeighbourhoodSystems.prod
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T))
      (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
        DomainTheory.NeighbourhoodSystems.Example23.T)
      (@DomainTheory.NeighbourhoodSystems.prodPresentation
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres)
      DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
      (@DomainTheory.NeighbourhoodSystems.Exercise724.pointwiseBin DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Example23.T
        DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.andT))
    (@And.intro
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
        DomainTheory.NeighbourhoodSystems.Exercise724.Gamma DomainTheory.NeighbourhoodSystems.Exercise724.L)
      (@DomainTheory.NeighbourhoodSystems.ComputableMap
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        (@DomainTheory.NeighbourhoodSystems.funSpace DomainTheory.NeighbourhoodSystems.Exercise724.Gamma
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise724.L
          DomainTheory.NeighbourhoodSystems.Example23.T)
        DomainTheory.NeighbourhoodSystems.Exercise724.LTpres DomainTheory.NeighbourhoodSystems.Exercise724.LTpres
        (@DomainTheory.NeighbourhoodSystems.Exercise724.postcompose DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Example23.T
          DomainTheory.NeighbourhoodSystems.Example23.T DomainTheory.NeighbourhoodSystems.Exercise724.notT))
      DomainTheory.NeighbourhoodSystems.Exercise724.L_isEffectivelyGiven
      DomainTheory.NeighbourhoodSystems.Exercise724.notT_lifted_isComputable)
    DomainTheory.NeighbourhoodSystems.Exercise724.andT_lifted_isComputable)
  DomainTheory.NeighbourhoodSystems.Exercise724.toElement_bijective
end

section
theorem LenumSubsetChar_le_one (t : ℕ) : LenumSubsetChar t ≤ 1 :=
  isPrefixChar_le_one _ _
end

section
theorem Lenum_subset_char_eq_one_iff (n m : ℕ) :
    Lenum n ⊆ Lenum m ↔ LenumSubsetChar (Nat.pair n m) = 1 := by
  unfold LenumSubsetChar
  rw [unpair_pair_fst, unpair_pair_snd, Lenum_subset_iff]
end

section
open DomainTheory.NeighbourhoodSystems.Example12 (Token zero one)

theorem T_isEffectivelyGiven : Example23.T.IsEffectivelyGiven := ⟨Tpres⟩

theorem TeqChar_eq_one_iff (a b : ℕ) : TeqChar a b = 1 ↔ a = b := by
  unfold TeqChar isZero; omega

end

section

theorem embStr_injective : Function.Injective embStr :=
  List.map_injective_iff.mpr bitToNat_injective
end

section
theorem primrec_LenumSubsetChar : Nat.Primrec LenumSubsetChar :=
  primrec_isPrefixChar_swap.of_eq fun t => by simp only [LenumSubsetChar]
end

section

theorem Lenum_subset_recDecidable : RecDecidable₂ (fun n m => Lenum n ⊆ Lenum m) :=
  RecDecidable₂.of_paired_zero_one_char primrec_LenumSubsetChar
    (fun t => by have := LenumSubsetChar_le_one t; omega)
    Lenum_subset_char_eq_one_iff
end

end DomainTheory.NeighbourhoodSystems.Exercise724
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

def codePair (a b : ℕ) : ℕ := Nat.pair (Nat.pair a b) 0 + 1
end

section
variable {α : Type*} {V : NeighborhoodSystem α}
variable (P : ComputablePresentation V)

def chainDec (fincl : ℕ → ℕ) (c : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, (b :: rest) => fincl (Nat.pair c (codePair a b)) = 1 ∧ chainDec fincl c b rest

def fixPStep (fincl : ℕ → ℕ) (c acc x : ℕ) : ℕ :=
  Nat.pair x (selectFn acc.unpair.2 (isOne (fincl (Nat.pair c (codePair acc.unpair.1 x)))) 0)

def fixStp (fincl : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair w.unpair.1
    (selectFn w.unpair.2.unpair.1.unpair.2
      (isOne (fincl (Nat.pair w.unpair.2.unpair.2
        (codePair w.unpair.2.unpair.1.unpair.1 w.unpair.1)))) 0)

def fixChainChar (fincl : ℕ → ℕ) (c i : ℕ) : ℕ :=
  foldCode (fixStp fincl) c (Nat.pair P.masterIdx 1) i

end

section
variable {α : Type*} {V : NeighborhoodSystem α}

def gLastOf : ℕ → List ℕ → ℕ
  | a, [] => a
  | _, (b :: rest) => gLastOf b rest

def gStepsOK (g : ApproximableMap V V) (P : ComputablePresentation V) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, (b :: rest) => g.rel (P.X a) (P.X b) ∧ gStepsOK g P b rest

end

section
variable {α : Type*} {V : NeighborhoodSystem α}
variable (P : ComputablePresentation V)

theorem Xenum_codePair (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (a b : ℕ) :
    Xenum P P gN (codePair a b) = step (P.X a) (P.X b) :=
  Xenum_singleton P P gN hgN a b

theorem fixPStep_foldl_fst (fincl : ℕ → ℕ) (c : ℕ) :
    ∀ (full : List ℕ) (prev fl : ℕ),
      (List.foldl (fixPStep fincl c) (Nat.pair prev fl) full).unpair.1 = gLastOf prev full := by
  intro full
  induction full with
  | nil =>
    intro prev fl
    show (Nat.pair prev fl).unpair.1 = prev
    exact unpair_pair_fst prev fl
  | cons b rest ih =>
    intro prev fl
    rw [List.foldl_cons]
    have hstep : fixPStep fincl c (Nat.pair prev fl) b
        = Nat.pair b (selectFn fl (isOne (fincl (Nat.pair c (codePair prev b)))) 0) := by
      unfold fixPStep; simp only [unpair_pair_fst, unpair_pair_snd]
    rw [hstep, ih b (selectFn fl (isOne (fincl (Nat.pair c (codePair prev b)))) 0)]
    rfl

theorem fixPStep_foldl_snd (fincl : ℕ → ℕ) (c : ℕ) :
    ∀ (full : List ℕ) (prev fl : ℕ), fl ≤ 1 →
      ((List.foldl (fixPStep fincl c) (Nat.pair prev fl) full).unpair.2 = 1 ↔
        fl = 1 ∧ chainDec fincl c prev full) := by
  intro full
  induction full with
  | nil =>
    intro prev fl _
    show (Nat.pair prev fl).unpair.2 = 1 ↔ fl = 1 ∧ chainDec fincl c prev []
    rw [unpair_pair_snd]
    simp [chainDec]
  | cons b rest ih =>
    intro prev fl _
    rw [List.foldl_cons]
    have hstep : fixPStep fincl c (Nat.pair prev fl) b
        = Nat.pair b (selectFn fl (isOne (fincl (Nat.pair c (codePair prev b)))) 0) := by
      unfold fixPStep; simp only [unpair_pair_fst, unpair_pair_snd]
    rw [hstep]
    set nf := selectFn fl (isOne (fincl (Nat.pair c (codePair prev b)))) 0 with hnf
    have hnfle : nf ≤ 1 := by
      rw [hnf]
      rcases (show fl = 0 ∨ fl = 1 by omega) with h | h <;> rw [h]
      · rw [selectFn_zero]; exact Nat.zero_le 1
      · rw [selectFn_one]; exact isOne_le_one _
    rw [ih b nf hnfle]
    have hnf1 : nf = 1 ↔ (fl = 1 ∧ fincl (Nat.pair c (codePair prev b)) = 1) := by
      rw [hnf]
      rcases (show fl = 0 ∨ fl = 1 by omega) with h | h <;> rw [h]
      · rw [selectFn_zero]; simp
      · rw [selectFn_one, isOne_eq_one_iff]; simp
    rw [hnf1]
    constructor
    · rintro ⟨⟨hfl1, hfincl1⟩, hrest⟩; exact ⟨hfl1, hfincl1, hrest⟩
    · rintro ⟨hfl1, hfincl1, hrest⟩; exact ⟨⟨hfl1, hfincl1⟩, hrest⟩

theorem fixStp_eq (fincl : ℕ → ℕ) (c acc x : ℕ) :
    fixStp fincl (Nat.pair x (Nat.pair acc c)) = fixPStep fincl c acc x := by
  unfold fixStp fixPStep
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem fixChainChar_eq (fincl : ℕ → ℕ) (c i : ℕ) :
    fixChainChar P fincl c i
      = List.foldl (fixPStep fincl c) (Nat.pair P.masterIdx 1) (decodeList i) := by
  unfold fixChainChar
  rw [foldCode_eq']
  have hstep : (fun acc x => fixStp fincl (Nat.pair x (Nat.pair acc c))) = fixPStep fincl c := by
    funext acc x; exact fixStp_eq fincl c acc x
  rw [hstep]

theorem fixChainChar_spec (fincl : ℕ → ℕ) (c i : ℕ) :
    (fixChainChar P fincl c i).unpair.1 = gLastOf P.masterIdx (decodeList i)
  ∧ ((fixChainChar P fincl c i).unpair.2 = 1 ↔ chainDec fincl c P.masterIdx (decodeList i)) := by
  rw [fixChainChar_eq]
  refine ⟨fixPStep_foldl_fst fincl c (decodeList i) P.masterIdx 1, ?_⟩
  rw [fixPStep_foldl_snd fincl c (decodeList i) P.masterIdx 1 (le_refl 1)]
  simp

end

section
variable {α : Type*} {V : NeighborhoodSystem α}

theorem gStepsOK_complete (g : ApproximableMap V V) (P : ComputablePresentation V) :
    ∀ (n a ℓ : ℕ), (g.iterMap n).rel (P.X a) (P.X ℓ) →
      ∃ full, gStepsOK g P a full ∧ P.X (gLastOf a full) ⊆ P.X ℓ := by
  intro n
  induction n with
  | zero =>
    intro a ℓ h
    rw [iterMap_zero, idMap_rel] at h
    exact ⟨[], trivial, h.2.2⟩
  | succ n ih =>
    intro a ℓ h
    have hcomm : g.iterMap (n + 1) = (g.iterMap n).comp g := by
      rw [iterMap_succ]; exact iter_comm g n
    rw [hcomm, comp_rel] at h
    obtain ⟨Y, h1, h2⟩ := h
    obtain ⟨k, hk⟩ := P.surj (g.rel_cod h1)
    rw [← hk] at h1 h2
    obtain ⟨full', hs', hl'⟩ := ih k ℓ h2
    exact ⟨k :: full', ⟨h1, hs'⟩, hl'⟩

theorem gStepsOK_sound (g : ApproximableMap V V) (P : ComputablePresentation V) :
    ∀ (full : List ℕ) (a : ℕ), gStepsOK g P a full →
      (g.iterMap full.length).rel (P.X a) (P.X (gLastOf a full)) := by
  intro full
  induction full with
  | nil =>
    intro a _
    show (g.iterMap ([] : List ℕ).length).rel (P.X a) (P.X a)
    rw [List.length_nil, iterMap_zero]
    exact idMap_rel.mpr ⟨P.mem_X a, P.mem_X a, subset_rfl⟩
  | cons b rest ih =>
    intro a hsteps
    obtain ⟨h1, hrest⟩ := hsteps
    have hcomm : g.iterMap (rest.length + 1) = (g.iterMap rest.length).comp g := by
      rw [iterMap_succ]; exact iter_comm g rest.length
    show (g.iterMap (b :: rest).length).rel (P.X a) (P.X (gLastOf b rest))
    rw [List.length_cons, hcomm, comp_rel]
    exact ⟨P.X b, h1, ih b hrest⟩

theorem fixElement_mem_iff_chain (g : ApproximableMap V V) (P : ComputablePresentation V)
    (a0 : ℕ) (ha0 : P.X a0 = V.master) (ℓ : ℕ) :
    g.fixElement.mem (P.X ℓ) ↔
      ∃ full, gStepsOK g P a0 full ∧ P.X (gLastOf a0 full) ⊆ P.X ℓ := by
  rw [mem_fixElement]
  constructor
  · rintro ⟨n, hn⟩
    rw [← ha0] at hn
    exact gStepsOK_complete g P n a0 ℓ hn
  · rintro ⟨full, hsteps, hlast⟩
    refine ⟨full.length, ?_⟩
    have hsound := gStepsOK_sound g P full a0 hsteps
    have hmono := (g.iterMap full.length).mono hsound subset_rfl hlast (P.mem_X a0) (P.mem_X ℓ)
    rwa [ha0] at hmono

end

section
variable {α : Type*} {V : NeighborhoodSystem α}
variable (P : ComputablePresentation V)

theorem fixMap_rel_iff (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (c ℓ : ℕ) :
    (fixMap V).rel (Xenum P P gN c) (P.X ℓ) ↔
      ∃ full : List ℕ,
        gStepsOK (toApproxMap ((funSpace V V).principal (Xenum_mem P P gN hgN c))) P P.masterIdx full
        ∧ P.X (gLastOf P.masterIdx full) ⊆ P.X ℓ := by
  rw [(fixMap V).rel_iff_mem_principal (Xenum_mem P P gN hgN c), fixMap_toElementMap]
  exact fixElement_mem_iff_chain _ P P.masterIdx P.masterIdx_spec ℓ

theorem leastMap_Xenum_rel (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (c a b : ℕ) :
    (toApproxMap ((funSpace V V).principal (Xenum_mem P P gN hgN c))).rel (P.X a) (P.X b)
      ↔ Xenum P P gN c ⊆ step (P.X a) (P.X b) := by
  rw [toApproxMap_rel, mem_principal]
  exact ⟨fun h => h.2, fun h => ⟨step_mem (P.mem_X a) (P.mem_X b), h⟩⟩

theorem chainDec_iff_gStepsOK (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
      : Set (ApproximableMap V V)).Nonempty) (fincl : ℕ → ℕ)
    (hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2) (c : ℕ) :
    ∀ (full : List ℕ) (a : ℕ),
      chainDec fincl c a full ↔
        gStepsOK (toApproxMap ((funSpace V V).principal (Xenum_mem P P gN hgN c))) P a full := by
  intro full
  induction full with
  | nil => intro a; exact Iff.rfl
  | cons b rest ih =>
    intro a
    constructor
    · rintro ⟨hstep, hrest⟩
      refine ⟨?_, (ih b).mp hrest⟩
      rw [hfincl, unpair_pair_fst, unpair_pair_snd, Xenum_codePair P gN hgN a b] at hstep
      exact (leastMap_Xenum_rel P gN hgN c a b).mpr hstep
    · rintro ⟨hstep, hrest⟩
      refine ⟨?_, (ih b).mpr hrest⟩
      have hsub : Xenum P P gN c ⊆ step (P.X a) (P.X b) :=
        (leastMap_Xenum_rel P gN hgN c a b).mp hstep
      rw [hfincl, unpair_pair_fst, unpair_pair_snd, Xenum_codePair P gN hgN a b]
      exact hsub

theorem primrec_fixStp (fincl : ℕ → ℕ) (hfinclp : Nat.Primrec fincl) :
    Nat.Primrec (fixStp fincl) := by
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hprev : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hflag : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hcode : Nat.Primrec (fun w : ℕ => codePair w.unpair.2.unpair.1.unpair.1 w.unpair.1) :=
    Nat.Primrec.succ.comp ((hprev.pair hx).pair (Nat.Primrec.const 0))
  have hinner : Nat.Primrec (fun w => Nat.pair w.unpair.2.unpair.2
      (codePair w.unpair.2.unpair.1.unpair.1 w.unpair.1)) := hc.pair hcode
  have hsel : Nat.Primrec (fun w => selectFn w.unpair.2.unpair.1.unpair.2
      (isOne (fincl (Nat.pair w.unpair.2.unpair.2
        (codePair w.unpair.2.unpair.1.unpair.1 w.unpair.1)))) 0) :=
    primrec_selectFn hflag (primrec_isOne.comp (hfinclp.comp hinner)) (Nat.Primrec.const 0)
  exact (hx.pair hsel).of_eq (fun _ => rfl)

theorem primrec_fixChainChar (fincl : ℕ → ℕ) (hfinclp : Nat.Primrec fincl) :
    Nat.Primrec (fun t => fixChainChar P fincl t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_fixStp fincl hfinclp) Nat.Primrec.left
    (Nat.Primrec.const (Nat.pair P.masterIdx 1)) Nat.Primrec.right).of_eq (fun _ => rfl)

end
end DomainTheory.NeighbourhoodSystems
end
