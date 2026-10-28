module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.atomU

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

section
open NeighborhoodSystem
variable {α : Type*}
variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)
variable (X : ℕ → Set α) (Δ : Set α)
variable (hΔ : Δ.Nonempty) (hsplit : SplitSpec split)
include hΔ hsplit

omit hΔ hsplit in
theorem transfer_dir {β1 β2 : Type*} (Z1 : ℕ → Set β1) (M1 : Set β1) (Z2 : ℕ → Set β2)
    (M2 : Set β2) (hcore : ∀ δ n, genAtom Z1 M1 δ n = ∅ ↔ genAtom Z2 M2 δ n = ∅)
    {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n)
    (hne : {x ∈ M1 | ∀ p ∈ cs, (p.2 = true ↔ x ∈ Z1 p.1)}.Nonempty) :
    {y ∈ M2 | ∀ p ∈ cs, (p.2 = true ↔ y ∈ Z2 p.1)}.Nonempty := by
  classical
  obtain ⟨x, hxM, hxcs⟩ := hne
  set δ0 : ℕ → Bool := fun k => decide (x ∈ Z1 k) with hδ0def
  have hX1 : x ∈ genAtom Z1 M1 δ0 n := genAtom_self Z1 M1 hxM n
  have hne1 : (genAtom Z1 M1 δ0 n).Nonempty := ⟨x, hX1⟩
  have hne2 : (genAtom Z2 M2 δ0 n).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h2 => hne1.ne_empty ((hcore δ0 n).mpr h2)
  obtain ⟨y, hy⟩ := hne2
  refine ⟨y, genAtom_subset Z2 M2 δ0 n hy, fun p hp => ?_⟩
  have hforward := genAtom_forward hy p.1 (hn p hp)
  have hbeq : δ0 p.1 = p.2 := by
    show decide (x ∈ Z1 p.1) = p.2
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact (hxcs p hp).symm
  rwa [hbeq] at hforward

theorem transfer_empty_iff {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n) :
    {x ∈ Δ | ∀ p ∈ cs, (p.2 = true ↔ x ∈ X p.1)}.Nonempty ↔
      {y ∈ U.master | ∀ p ∈ cs, (p.2 = true ↔ y ∈ Yseq split X Δ p.1)}.Nonempty := by
  have hcore : ∀ δ n, genAtom X Δ δ n = ∅ ↔ genAtom (Yseq split X Δ) U.master δ n = ∅ :=
    fun δ n => (atomU_invariant split X Δ hΔ hsplit n).1 δ
      |>.trans (by rw [atomU_eq_genAtom split X Δ hΔ hsplit])
  have hcore' : ∀ δ n, genAtom (Yseq split X Δ) U.master δ n = ∅ ↔ genAtom X Δ δ n = ∅ :=
    fun δ n => (hcore δ n).symm
  exact ⟨transfer_dir X Δ (Yseq split X Δ) U.master hcore hn,
    transfer_dir (Yseq split X Δ) U.master X Δ hcore' hn⟩

theorem transfer_subset_iff (i j : ℕ) :
    Δ ∩ X i ⊆ X j ↔ U.master ∩ Yseq split X Δ i ⊆ Yseq split X Δ j := by
  have key := transfer_empty_iff split X Δ hΔ hsplit (cs := [(i, true), (j, false)])
    (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ Δ | ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ x ∈ X p.1)}
      = (Δ ∩ X i) \ X j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master |
      ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ y ∈ Yseq split X Δ p.1)}
      = (U.master ∩ Yseq split X Δ i) \ Yseq split X Δ j := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

theorem transfer_inter_empty_iff (i j : ℕ) :
    Δ ∩ X i ∩ X j = ∅ ↔ U.master ∩ Yseq split X Δ i ∩ Yseq split X Δ j = ∅ := by
  have key := transfer_empty_iff split X Δ hΔ hsplit (cs := [(i, true), (j, true)])
    (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ Δ | ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ x ∈ X p.1)}
      = Δ ∩ X i ∩ X j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master | ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ y ∈ Yseq split X Δ p.1)}
      = U.master ∩ Yseq split X Δ i ∩ Yseq split X Δ j := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

theorem transfer_double_subset_iff (i j k : ℕ) :
    Δ ∩ X i ∩ X j ⊆ X k ↔ U.master ∩ Yseq split X Δ i ∩ Yseq split X Δ j ⊆ Yseq split X Δ k := by
  have key := transfer_empty_iff split X Δ hΔ hsplit (cs := [(i, true), (j, true), (k, false)])
    (n := max i (max j k) + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;>
          simp [(Nat.le_max_left j k).trans (Nat.le_max_right i (max j k)),
            (Nat.le_max_right j k).trans (Nat.le_max_right i (max j k))])
  have hLHS : {x ∈ Δ | ∀ p ∈ [(i, true), (j, true), (k, false)], (p.2 = true ↔ x ∈ X p.1)}
      = (Δ ∩ X i ∩ X j) \ X k := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master |
      ∀ p ∈ [(i, true), (j, true), (k, false)], (p.2 = true ↔ y ∈ Yseq split X Δ p.1)}
      = (U.master ∩ Yseq split X Δ i ∩ Yseq split X Δ j) \ Yseq split X Δ k := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

theorem Yseq_subset_master (n : ℕ) : Yseq split X Δ n ⊆ U.master :=
  Set.iUnion_subset fun δ' => atomU_subset_master split X Δ hΔ hsplit (extendTrue δ') (n + 1)

theorem Yseq_zero_eq_master (h0 : X 0 = Δ) : Yseq split X Δ 0 = U.master := by
  set δ : ℕ → Bool := extendTrue (fun i : Fin 0 => i.elim0) with hδdef
  have hδ0 : δ 0 = true := by simp [hδdef, extendTrue]
  have hAB : genAtom X Δ δ 0 = ∅ ↔ atomU split X Δ δ 0 = ∅ :=
    ⟨fun h => absurd h hΔ.ne_empty, fun h => absurd h U.master_mem.2.1.ne_empty⟩
  have hBU : atomU split X Δ δ 0 = ∅ ∨ U.mem (atomU split X Δ δ 0) := Or.inr U.master_mem
  have hspec := hsplit hAB hBU (X 0)
  have hJ : (split (genAtom X Δ δ 0) (atomU split X Δ δ 0) (X 0)).2 = ∅ := by
    rw [← hspec.2.2.2.1]
    show genAtom X Δ δ 0 \ X 0 = ∅
    rw [show genAtom X Δ δ 0 = Δ from rfl, h0]
    exact Set.sdiff_self
  have hI : (split (genAtom X Δ δ 0) (atomU split X Δ δ 0) (X 0)).1 = U.master := by
    have hunion := hspec.2.2.2.2.1
    rw [hJ, Set.union_empty] at hunion
    exact hunion
  have hkey : atomU split X Δ δ 1 = U.master := by rw [atomU_succ, hδ0, ite_eq_left rfl]; exact hI
  apply Set.Subset.antisymm (Yseq_subset_master split X Δ hΔ hsplit 0)
  calc U.master = atomU split X Δ δ 1 := hkey.symm
    _ ⊆ Yseq split X Δ 0 := subset_Yseq split X Δ (fun i : Fin 0 => i.elim0)

theorem transfer_inter_eq_iff (i j k : ℕ) (hi : X i ⊆ Δ) (_hj : X j ⊆ Δ) (hk : X k ⊆ Δ) :
    X i ∩ X j = X k ↔ Yseq split X Δ i ∩ Yseq split X Δ j = Yseq split X Δ k := by
  have h1 : X k ⊆ X i ↔ Yseq split X Δ k ⊆ Yseq split X Δ i := by
    have := transfer_subset_iff split X Δ hΔ hsplit k i
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right (Yseq_subset_master split X Δ hΔ hsplit k)] at this
  have h2 : X k ⊆ X j ↔ Yseq split X Δ k ⊆ Yseq split X Δ j := by
    have := transfer_subset_iff split X Δ hΔ hsplit k j
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right (Yseq_subset_master split X Δ hΔ hsplit k)] at this
  have h3 : X i ∩ X j ⊆ X k ↔ Yseq split X Δ i ∩ Yseq split X Δ j ⊆ Yseq split X Δ k := by
    have := transfer_double_subset_iff split X Δ hΔ hsplit i j k
    rwa [Set.inter_eq_self_of_subset_right hi,
      Set.inter_eq_self_of_subset_right (Yseq_subset_master split X Δ hΔ hsplit i)] at this
  constructor
  · intro heq
    have hki : X k ⊆ X i := heq ▸ Set.inter_subset_left
    have hkj : X k ⊆ X j := heq ▸ Set.inter_subset_right
    have hijk : X i ∩ X j ⊆ X k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mp hijk) (Set.subset_inter (h1.mp hki) (h2.mp hkj))
  · intro heq
    have hki : Yseq split X Δ k ⊆ Yseq split X Δ i := heq ▸ Set.inter_subset_left
    have hkj : Yseq split X Δ k ⊆ Yseq split X Δ j := heq ▸ Set.inter_subset_right
    have hijk : Yseq split X Δ i ∩ Yseq split X Δ j ⊆ Yseq split X Δ k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mpr hijk) (Set.subset_inter (h1.mpr hki) (h2.mpr hkj))

theorem Yseq_empty_or_mem (n : ℕ) : Yseq split X Δ n = ∅ ∨ U.mem (Yseq split X Δ n) := by
  by_cases hne : (Yseq split X Δ n).Nonempty
  · exact Or.inr (U.iUnion_mem
      (fun δ' => (atomU_invariant split X Δ hΔ hsplit (n + 1)).2.1 (extendTrue δ')) hne)
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

theorem Yseq_nonempty_of_mem {n : ℕ} {x : α} (hxΔ : x ∈ Δ) (hxn : x ∈ X n) :
    (Yseq split X Δ n).Nonempty := by
  classical
  set δ0 : ℕ → Bool := fun k => decide (x ∈ X k) with hδ0def
  have hδ0n : δ0 n = true := by show decide (x ∈ X n) = true; rw [decide_eq_true_iff]; exact hxn
  have hxA : x ∈ genAtom X Δ δ0 n := genAtom_self X Δ hxΔ n
  have hAX : x ∈ genAtom X Δ δ0 n ∩ X n := ⟨hxA, hxn⟩
  have hAne : (genAtom X Δ δ0 n ∩ X n).Nonempty := ⟨x, hAX⟩
  obtain ⟨hmatch, hmem, -⟩ := atomU_invariant split X Δ hΔ hsplit n
  have hspec := hsplit (hmatch δ0) (hmem δ0) (X n)
  have hIne : (split (genAtom X Δ δ0 n) (atomU split X Δ δ0 n) (X n)).1 ≠ ∅ :=
    fun h => hAne.ne_empty (hspec.2.2.1.mpr h)
  have hI_eq_atomU : (split (genAtom X Δ δ0 n) (atomU split X Δ δ0 n) (X n)).1 =
      atomU split X Δ δ0 (n + 1) := by rw [atomU_succ, hδ0n, ite_eq_left rfl]
  set δ2 : ℕ → Bool := extendTrue (restrictFin δ0 n) with hδ2def
  have hagree : ∀ i < n + 1, δ2 i = δ0 i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact extendTrue_restrictFin_agree δ0 n i hi'
    · simp [hδ2def, extendTrue, hδ0n]
  have hδ2_eq : atomU split X Δ δ2 (n + 1) = atomU split X Δ δ0 (n + 1) :=
    atomU_congr split X Δ hagree
  have hne2 : (atomU split X Δ δ2 (n + 1)).Nonempty := by
    rw [hδ2_eq, ← hI_eq_atomU]
    exact Set.nonempty_iff_ne_empty.mpr hIne
  exact hne2.mono (subset_Yseq split X Δ (restrictFin δ0 n))

end

section
open NeighborhoodSystem
variable {α : Type*}

open Classical in

open Classical in

theorem splitChoice_isSplitSpec : SplitSpec (α := α) splitChoice := by
  intro A B hAB hBU Xn
  classical
  unfold splitChoice
  rw [dite_eq_left ⟨hAB, hBU⟩]
  exact (exists_split hAB hBU Xn).choose_spec.choose_spec

end

end DomainTheory.NeighbourhoodSystems
