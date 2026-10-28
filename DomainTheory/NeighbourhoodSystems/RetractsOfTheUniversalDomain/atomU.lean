module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitSpec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

section
open NeighborhoodSystem
variable {α : Type*}
variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)

noncomputable def atomU (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)
    (X : ℕ → Set α) (Δ : Set α) (δ : ℕ → Bool) : ℕ → Set ℚ
  | 0 => U.master
  | (n + 1) =>
      if δ n then (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).2
end

section
open NeighborhoodSystem
variable {α : Type*}
variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)
variable (X : ℕ → Set α) (Δ : Set α)

@[simp] theorem atomU_zero (δ : ℕ → Bool) : atomU split X Δ δ 0 = U.master := rfl
end

section
open NeighborhoodSystem
variable {α : Type*}
variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)
variable (X : ℕ → Set α) (Δ : Set α)
variable (hΔ : Δ.Nonempty) (hsplit : SplitSpec split)
include hΔ hsplit

def extendTrue {n : ℕ} (δ' : Fin n → Bool) : ℕ → Bool :=
  fun i => if h : i < n then δ' ⟨i, h⟩ else true

noncomputable def Yseq (n : ℕ) : Set ℚ :=
  ⋃ δ' : Fin n → Bool, atomU split X Δ (extendTrue δ') (n + 1)

def restrictFin (δ : ℕ → Bool) (n : ℕ) : Fin n → Bool := fun i => δ i.val

end

section
open NeighborhoodSystem
variable {α : Type*}

open Classical in

noncomputable def splitChoice (A : Set α) (B : Set ℚ) (Xn : Set α) : Set ℚ × Set ℚ :=
  if h : (A = ∅ ↔ B = ∅) ∧ (B = ∅ ∨ U.mem B) then
    ⟨(exists_split h.1 h.2 Xn).choose, (exists_split h.1 h.2 Xn).choose_spec.choose⟩
  else (∅, ∅)

theorem genAtom_subset {β : Type*} (Z : ℕ → Set β) (M : Set β) (δ : ℕ → Bool) (n : ℕ) :
    genAtom Z M δ n ⊆ M := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (Set.inter_subset_left).trans ih

theorem genAtom_congr {β : Type*} (Z : ℕ → Set β) (M : Set β) {δ δ' : ℕ → Bool} {n : ℕ}
    (h : ∀ i < n, δ i = δ' i) : genAtom Z M δ n = genAtom Z M δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := h n (Nat.lt_succ_self n)
    have hprev : genAtom Z M δ n = genAtom Z M δ' n := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    show genAtom Z M δ n ∩ _ = genAtom Z M δ' n ∩ _
    rw [hprev, hn]

theorem genAtom_forward {β : Type*} {Z : ℕ → Set β} {M : Set β} {δ : ℕ → Bool} {n : ℕ}
    {x : β} (hx : x ∈ genAtom Z M δ n) : ∀ i < n, (δ i = true ↔ x ∈ Z i) := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    obtain ⟨hxprev, hxlast⟩ := hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact ih hxprev i hi'
    · by_cases hδ : δ i = true
      · simp only [hδ, ite_true] at hxlast
        exact ⟨fun _ => hxlast, fun _ => hδ⟩
      · rw [Bool.not_eq_true] at hδ
        simp only [hδ] at hxlast
        exact ⟨fun h => absurd h (by simp [hδ]), fun hmem => absurd hmem hxlast.2⟩

open Classical in

theorem genAtom_self {β : Type*} (Z : ℕ → Set β) (M : Set β) {x : β} (hx : x ∈ M) :
    ∀ n, x ∈ genAtom Z M (fun k => decide (x ∈ Z k)) n := by
  intro n
  induction n with
  | zero => exact hx
  | succ n ih =>
    refine ⟨ih, ?_⟩
    by_cases h : x ∈ Z n
    · simp [h]
    · simp [h, hx]

theorem split_fst_subset {split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ} (hsplit : SplitSpec split)
    {A : Set α} {B : Set ℚ} (hAB : A = ∅ ↔ B = ∅)
    (hBU : B = ∅ ∨ U.mem B) (Xn : Set α) : (split A B Xn).1 ⊆ B :=
  Set.subset_union_left.trans_eq (hsplit hAB hBU Xn).2.2.2.2.1

theorem split_snd_subset {split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ} (hsplit : SplitSpec split)
    {A : Set α} {B : Set ℚ} (hAB : A = ∅ ↔ B = ∅)
    (hBU : B = ∅ ∨ U.mem B) (Xn : Set α) : (split A B Xn).2 ⊆ B :=
  Set.subset_union_right.trans_eq (hsplit hAB hBU Xn).2.2.2.2.1

variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)

variable (X : ℕ → Set α) (Δ : Set α)

theorem atomU_succ (δ : ℕ → Bool) (n : ℕ) :
    atomU split X Δ δ (n + 1) =
      if δ n then (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).2 := rfl

theorem atomU_congr {δ δ' : ℕ → Bool} {n : ℕ} (h : ∀ i < n, δ i = δ' i) :
    atomU split X Δ δ n = atomU split X Δ δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : atomU split X Δ δ n = atomU split X Δ δ' n :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hA : genAtom X Δ δ n = genAtom X Δ δ' n :=
      genAtom_congr X Δ (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn := h n (Nat.lt_succ_self n)
    rw [atomU_succ, atomU_succ, hA, hprev, hn]

variable (hΔ : Δ.Nonempty) (hsplit : SplitSpec split)
include hΔ hsplit

theorem atomU_invariant :
    ∀ n, (∀ δ, genAtom X Δ δ n = ∅ ↔ atomU split X Δ δ n = ∅) ∧
      (∀ δ, atomU split X Δ δ n = ∅ ∨ U.mem (atomU split X Δ δ n)) ∧
      (∀ δ δ', (∃ i < n, δ i ≠ δ' i) →
        atomU split X Δ δ n ∩ atomU split X Δ δ' n = ∅) := by
  have hUmasterNe : (U.master : Set ℚ) ≠ ∅ := Set.Nonempty.ne_empty ⟨0, by norm_num [U]⟩
  intro n
  induction n with
  | zero =>
    refine ⟨fun δ => ?_, fun δ => Or.inr U.master_mem, fun δ δ' ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
    show Δ = ∅ ↔ (U.master : Set ℚ) = ∅
    exact ⟨fun h => absurd h hΔ.ne_empty, fun h => absurd h hUmasterNe⟩
  | succ n ih =>
    obtain ⟨ihmatch, ihmem, ihdisj⟩ := ih
    refine ⟨fun δ => ?_, fun δ => ?_, fun δ δ' ⟨i, hi, hne⟩ => ?_⟩
    · have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
      rw [atomU_succ]
      by_cases hδ : δ n = true
      · rw [show genAtom X Δ δ (n + 1) = genAtom X Δ δ n ∩ X n from by simp [genAtom, hδ]]
        simp only [hδ, ite_true]
        exact hspec.2.2.1
      · rw [Bool.not_eq_true] at hδ
        have hsub := genAtom_subset X Δ δ n
        rw [show genAtom X Δ δ (n + 1) = genAtom X Δ δ n \ X n from by
          have heq : genAtom X Δ δ (n + 1) = genAtom X Δ δ n ∩ (Δ \ X n) := by simp [genAtom, hδ]
          rw [heq]
          ext x; constructor
          · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩
          · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩]
        simp only [hδ]
        exact hspec.2.2.2.1
    · have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
      rw [atomU_succ]
      by_cases hδ : δ n = true
      · simp only [hδ, ite_true]; exact hspec.1
      · simp only [hδ]; exact hspec.2.1
    · by_cases hagree : ∀ j < n, δ j = δ' j
      · have hδn : δ n ≠ δ' n := by
          intro heq
          exact hne (by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
            · exact hagree i hi'
            · exact heq)
        have hA : genAtom X Δ δ n = genAtom X Δ δ' n := genAtom_congr X Δ hagree
        have hB : atomU split X Δ δ n = atomU split X Δ δ' n := atomU_congr split X Δ hagree
        have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
        rw [atomU_succ, atomU_succ, hA, hB]
        have hIJ := hspec.2.2.2.2.2
        rcases Bool.eq_false_or_eq_true (δ n) with h1 | h1 <;>
          rcases Bool.eq_false_or_eq_true (δ' n) with h2 | h2 <;>
          simp_all [Set.inter_comm]
      · push Not at hagree
        obtain ⟨j, hj, hjne⟩ := hagree
        have hd : atomU split X Δ δ n ∩ atomU split X Δ δ' n = ∅ := ihdisj δ δ' ⟨j, hj, hjne⟩
        have h1 : atomU split X Δ δ (n + 1) ⊆ atomU split X Δ δ n := by
          rw [atomU_succ]
          by_cases hδ : δ n = true
          · simp only [hδ, ite_true]; exact split_fst_subset hsplit (ihmatch δ) (ihmem δ) (X n)
          · simp only [hδ]; exact split_snd_subset hsplit (ihmatch δ) (ihmem δ) (X n)
        have h2 : atomU split X Δ δ' (n + 1) ⊆ atomU split X Δ δ' n := by
          rw [atomU_succ]
          by_cases hδ' : δ' n = true
          · simp only [hδ', ite_true]; exact split_fst_subset hsplit (ihmatch δ') (ihmem δ') (X n)
          · simp only [hδ']; exact split_snd_subset hsplit (ihmatch δ') (ihmem δ') (X n)
        exact Set.subset_eq_empty (Set.inter_subset_inter h1 h2) hd

theorem atomU_succ_subset (δ : ℕ → Bool) (n : ℕ) :
    atomU split X Δ δ (n + 1) ⊆ atomU split X Δ δ n := by
  obtain ⟨hmatch, hmem, -⟩ := atomU_invariant split X Δ hΔ hsplit n
  rw [atomU_succ]
  by_cases hδ : δ n = true
  · simp only [hδ, ite_true]; exact split_fst_subset hsplit (hmatch δ) (hmem δ) (X n)
  · simp only [hδ]; exact split_snd_subset hsplit (hmatch δ) (hmem δ) (X n)

omit hΔ hsplit in
theorem extendTrue_agree {n : ℕ} (δ' : Fin n → Bool) (i : ℕ) (hi : i < n) :
    extendTrue δ' i = δ' ⟨i, hi⟩ := by simp [extendTrue, hi]

omit hΔ hsplit in
theorem extendTrue_restrictFin_agree (δ : ℕ → Bool) (n i : ℕ) (hi : i < n) :
    extendTrue (restrictFin δ n) i = δ i := by simp [extendTrue, restrictFin, hi]

omit hΔ hsplit in
theorem subset_Yseq {n : ℕ} (δ' : Fin n → Bool) :
    atomU split X Δ (extendTrue δ') (n + 1) ⊆ Yseq split X Δ n :=
  Set.subset_iUnion (fun δ' => atomU split X Δ (extendTrue δ') (n + 1)) δ'

theorem split_fst_eq_inter_Yseq (δ : ℕ → Bool) (n : ℕ) :
    (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1 =
      atomU split X Δ δ n ∩ Yseq split X Δ n := by
  obtain ⟨hmatch, hmem, hdisj⟩ := atomU_invariant split X Δ hΔ hsplit n
  set A := genAtom X Δ δ n with hAdef
  set B := atomU split X Δ δ n with hBdef
  set I := (split A B (X n)).1 with hIdef
  set δ2 := Function.update δ n true with hδ2def
  set δ3 := extendTrue (restrictFin δ2 n) with hδ3def
  have hagreefull : ∀ i < n + 1, δ3 i = δ2 i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact extendTrue_restrictFin_agree δ2 n i hi'
    · simp [hδ3def, extendTrue, hδ2def]
  have hI_eq : atomU split X Δ δ2 (n + 1) = I := by
    rw [atomU_succ]
    have hd2n : δ2 n = true := by simp [hδ2def]
    have hA2 : genAtom X Δ δ2 n = A := by
      apply genAtom_congr; intro i hi; simp [hδ2def, Function.update_of_ne (ne_of_lt hi)]
    have hB2 : atomU split X Δ δ2 n = B := by
      apply atomU_congr; intro i hi; simp [hδ2def, Function.update_of_ne (ne_of_lt hi)]
    rw [hd2n, ite_eq_left rfl, hA2, hB2]
  have hδ3_eq : atomU split X Δ δ3 (n + 1) = I := (atomU_congr split X Δ hagreefull).trans hI_eq
  apply Set.Subset.antisymm
  · have hIsubB : I ⊆ B := split_fst_subset hsplit (hmatch δ) (hmem δ) (X n)
    have hIsubY : I ⊆ Yseq split X Δ n := hδ3_eq ▸ subset_Yseq split X Δ (restrictFin δ2 n)
    exact Set.subset_inter hIsubB hIsubY
  · rintro z ⟨hzB, hzY⟩
    obtain ⟨δ', hz'⟩ := Set.mem_iUnion.mp hzY
    by_cases hagree : ∀ i < n, extendTrue δ' i = δ i
    · have hAeq : genAtom X Δ (extendTrue δ') n = A := genAtom_congr X Δ hagree
      have hBeq : atomU split X Δ (extendTrue δ') n = B := atomU_congr split X Δ hagree
      have hlast : extendTrue δ' n = true := by simp [extendTrue]
      have heq : atomU split X Δ (extendTrue δ') (n + 1) = I := by
        rw [atomU_succ, hAeq, hBeq, hlast, ite_eq_left rfl]
      rwa [heq] at hz'
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hzB' : z ∈ atomU split X Δ (extendTrue δ') n :=
        atomU_succ_subset split X Δ hΔ hsplit (extendTrue δ') n hz'
      have hempty := hdisj δ (extendTrue δ') ⟨j, hj, fun h => hjne (h.symm)⟩
      exact absurd (Set.mem_inter hzB hzB') (by rw [hempty]; simp)

theorem atomU_subset_master (δ : ℕ → Bool) (n : ℕ) : atomU split X Δ δ n ⊆ U.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomU_succ_subset split X Δ hΔ hsplit δ n).trans ih

theorem atomU_succ_eq (δ : ℕ → Bool) (n : ℕ) :
    atomU split X Δ δ (n + 1) =
      atomU split X Δ δ n ∩ (if δ n then Yseq split X Δ n else U.master \ Yseq split X Δ n) := by
  obtain ⟨hmatch, hmem, -⟩ := atomU_invariant split X Δ hΔ hsplit n
  have hspec := hsplit (hmatch δ) (hmem δ) (X n)
  have hIeq := split_fst_eq_inter_Yseq split X Δ hΔ hsplit δ n
  by_cases hδ : δ n = true
  · rw [atomU_succ, ite_eq_left hδ, ite_eq_left hδ]; exact hIeq
  · rw [atomU_succ, ite_eq_right hδ, ite_eq_right hδ]
    have hJeq : (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).2 =
        atomU split X Δ δ n \ Yseq split X Δ n := by
      have hunion := hspec.2.2.2.2.1
      have hinter := hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxB : x ∈ atomU split X Δ δ n := hunion ▸ Or.inr hxJ
        refine ⟨hxB, fun hxY => ?_⟩
        have hxI : x ∈ (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1 :=
          hIeq ▸ Set.mem_inter hxB hxY
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxB, hxnY⟩
        rw [← hunion] at hxB
        rcases hxB with hxI | hxJ
        · exact absurd (hIeq ▸ hxI : x ∈ atomU split X Δ δ n ∩ Yseq split X Δ n).2 hxnY
        · exact hxJ
    rw [hJeq]
    have hsub := atomU_subset_master split X Δ hΔ hsplit δ n
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

theorem atomU_eq_genAtom (δ : ℕ → Bool) :
    ∀ n, atomU split X Δ δ n = genAtom (Yseq split X Δ) U.master δ n
  | 0 => rfl
  | (n + 1) => by
      rw [atomU_succ_eq split X Δ hΔ hsplit, atomU_eq_genAtom δ n]; rfl

end

end DomainTheory.NeighbourhoodSystems
