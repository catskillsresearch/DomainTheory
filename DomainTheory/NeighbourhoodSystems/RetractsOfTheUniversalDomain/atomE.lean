module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.domainIso812c

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

/-- The `E`-side atom matching `genAtom X Δ δ n`, built recursively via an abstract splitting
operation `split` satisfying `SplitSpec' E split`. Generalizes `Theorem88.lean`'s `atomU` from the
hardcoded target `U` to an abstract `E`. -/
noncomputable def atomE {α γ : Type*} (E : NeighborhoodSystem γ)
    (split : Set α → Set γ → Set α → Set γ × Set γ)
    (X : ℕ → Set α) (Δ : Set α) (δ : ℕ → Bool) : ℕ → Set γ
  | 0 => E.master
  | (n + 1) =>
      if δ n then (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).2

section
variable {α γ : Type*}
variable (E : NeighborhoodSystem γ) (split : Set α → Set γ → Set α → Set γ × Set γ)
variable (X : ℕ → Set α) (Δ : Set α)

/-- **The abstract analogue of Scott's `Yₙ`**: the union, over all `2ⁿ` depth-`n` atoms, of the
"+"-piece chosen when splitting against `X n`. Generalizes `Theorem88.lean`'s `Yseq`. -/
noncomputable def YseqE (n : ℕ) : Set γ :=
  ⋃ δ' : Fin n → Bool, atomE E split X Δ (extendTrue δ') (n + 1)

namespace atomE

@[simp] theorem zero (δ : ℕ → Bool) : atomE E split X Δ δ 0 = E.master := rfl

theorem succ (δ : ℕ → Bool) (n : ℕ) :
    atomE E split X Δ δ (n + 1) =
      if δ n then (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).2 := rfl

/-- Extending/changing `δ` at or beyond position `n` does not change `atomE E split X Δ δ n`
(mirrors `atomU_congr`). -/
theorem congr {δ δ' : ℕ → Bool} {n : ℕ} (h : ∀ i < n, δ i = δ' i) :
    atomE E split X Δ δ n = atomE E split X Δ δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : atomE E split X Δ δ n = atomE E split X Δ δ' n :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hA : genAtom X Δ δ n = genAtom X Δ δ' n :=
      genAtom_congr X Δ (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn := h n (Nat.lt_succ_self n)
    rw [succ, succ, hA, hprev, hn]

end atomE

variable (hΔ : Δ.Nonempty) (hEmne : E.master.Nonempty) (hsplit : SplitSpec' E split)
include hΔ hEmne hsplit

namespace atomE

/-- **The core invariant, generalizing `atomU_invariant`.** At every depth `n` and for every sign
sequence `δ`: (a) the atom-matching invariant (`genAtom X Δ δ n = ∅ ↔ atomE E split X Δ δ n = ∅`),
(b) `atomE E split X Δ δ n` is either empty or a genuine `E`-neighbourhood, and (c) pairwise
disjointness for sign sequences disagreeing somewhere below `n`. -/
theorem invariant :
    ∀ n, (∀ δ, genAtom X Δ δ n = ∅ ↔ atomE E split X Δ δ n = ∅) ∧
      (∀ δ, atomE E split X Δ δ n = ∅ ∨ E.mem (atomE E split X Δ δ n)) ∧
      (∀ δ δ', (∃ i < n, δ i ≠ δ' i) →
        atomE E split X Δ δ n ∩ atomE E split X Δ δ' n = ∅) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun δ => ?_, fun δ => Or.inr E.master_mem,
      fun δ δ' ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
    show Δ = ∅ ↔ (E.master : Set γ) = ∅
    exact ⟨fun h => absurd h hΔ.ne_empty, fun h => absurd h hEmne.ne_empty⟩
  | succ n ih =>
    obtain ⟨ihmatch, ihmem, ihdisj⟩ := ih
    refine ⟨fun δ => ?_, fun δ => ?_, fun δ δ' ⟨i, hi, hne⟩ => ?_⟩
    · have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
      rw [succ]
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
      rw [succ]
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
        have hB : atomE E split X Δ δ n = atomE E split X Δ δ' n := congr E split X Δ hagree
        have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
        rw [succ, succ, hA, hB]
        have hIJ := hspec.2.2.2.2.2
        rcases Bool.eq_false_or_eq_true (δ n) with h1 | h1 <;>
          rcases Bool.eq_false_or_eq_true (δ' n) with h2 | h2 <;>
          simp_all [Set.inter_comm]
      · push Not at hagree
        obtain ⟨j, hj, hjne⟩ := hagree
        have hd : atomE E split X Δ δ n ∩ atomE E split X Δ δ' n = ∅ := ihdisj δ δ' ⟨j, hj, hjne⟩
        have h1 : atomE E split X Δ δ (n + 1) ⊆ atomE E split X Δ δ n := by
          rw [succ]
          by_cases hδ : δ n = true
          · simp only [hδ, ite_true]; exact split_fst_subset' hsplit (ihmatch δ) (ihmem δ) (X n)
          · simp only [hδ]; exact split_snd_subset' hsplit (ihmatch δ) (ihmem δ) (X n)
        have h2 : atomE E split X Δ δ' (n + 1) ⊆ atomE E split X Δ δ' n := by
          rw [succ]
          by_cases hδ' : δ' n = true
          · simp only [hδ', ite_true]; exact split_fst_subset' hsplit (ihmatch δ') (ihmem δ') (X n)
          · simp only [hδ']; exact split_snd_subset' hsplit (ihmatch δ') (ihmem δ') (X n)
        exact Set.subset_eq_empty (Set.inter_subset_inter h1 h2) hd

/-- Corollary of `atomE.invariant`, extracted for reuse: `atomE` only shrinks as `n` grows
(mirrors `atomU_succ_subset`). -/
theorem succ_subset (δ : ℕ → Bool) (n : ℕ) :
    atomE E split X Δ δ (n + 1) ⊆ atomE E split X Δ δ n := by
  obtain ⟨hmatch, hmem, -⟩ := invariant E split X Δ hΔ hEmne hsplit n
  rw [succ]
  by_cases hδ : δ n = true
  · simp only [hδ, ite_true]; exact split_fst_subset' hsplit (hmatch δ) (hmem δ) (X n)
  · simp only [hδ]; exact split_snd_subset' hsplit (hmatch δ) (hmem δ) (X n)

/-- `atomE E split X Δ δ n` is always a subset of `E.master` (mirrors `atomU_subset_master`). -/
theorem subset_master (δ : ℕ → Bool) (n : ℕ) : atomE E split X Δ δ n ⊆ E.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (succ_subset E split X Δ hΔ hEmne hsplit δ n).trans ih

end atomE

/-- **The "I-formula", generalizing `split_fst_eq_inter_Yseq`**: the "+"-piece chosen when
splitting the depth-`n` atom for `δ` against `X n` is *exactly* the intersection of that atom with
`YseqE E split X Δ n`. -/
theorem split_fst_eq_inter_YseqE (δ : ℕ → Bool) (n : ℕ) :
    (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).1 =
      atomE E split X Δ δ n ∩ YseqE E split X Δ n := by
  obtain ⟨hmatch, hmem, hdisj⟩ := atomE.invariant E split X Δ hΔ hEmne hsplit n
  set A := genAtom X Δ δ n with hAdef
  set B := atomE E split X Δ δ n with hBdef
  set I := (split A B (X n)).1 with hIdef
  set δ2 := Function.update δ n true with hδ2def
  set δ3 := extendTrue (restrictFin δ2 n) with hδ3def
  have hagreefull : ∀ i < n + 1, δ3 i = δ2 i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact extendTrue_restrictFin_agree δ2 n i hi'
    · simp [hδ3def, extendTrue, hδ2def]
  have hI_eq : atomE E split X Δ δ2 (n + 1) = I := by
    rw [atomE.succ]
    have hd2n : δ2 n = true := by simp [hδ2def]
    have hA2 : genAtom X Δ δ2 n = A := by
      apply genAtom_congr; intro i hi; simp [hδ2def, Function.update_of_ne (ne_of_lt hi)]
    have hB2 : atomE E split X Δ δ2 n = B := by
      apply atomE.congr; intro i hi; simp [hδ2def, Function.update_of_ne (ne_of_lt hi)]
    rw [hd2n, ite_eq_left rfl, hA2, hB2]
  have hδ3_eq : atomE E split X Δ δ3 (n + 1) = I := (atomE.congr E split X Δ hagreefull).trans hI_eq
  apply Set.Subset.antisymm
  · have hIsubB : I ⊆ B := split_fst_subset' hsplit (hmatch δ) (hmem δ) (X n)
    have hIsubY : I ⊆ YseqE E split X Δ n :=
      hδ3_eq ▸ Set.subset_iUnion (fun δ' => atomE E split X Δ (extendTrue δ') (n + 1))
        (restrictFin δ2 n)
    exact Set.subset_inter hIsubB hIsubY
  · rintro z ⟨hzB, hzY⟩
    obtain ⟨δ', hz'⟩ := Set.mem_iUnion.mp hzY
    by_cases hagree : ∀ i < n, extendTrue δ' i = δ i
    · have hAeq : genAtom X Δ (extendTrue δ') n = A := genAtom_congr X Δ hagree
      have hBeq : atomE E split X Δ (extendTrue δ') n = B := atomE.congr E split X Δ hagree
      have hlast : extendTrue δ' n = true := by simp [extendTrue]
      have heq : atomE E split X Δ (extendTrue δ') (n + 1) = I := by
        rw [atomE.succ, hAeq, hBeq, hlast, ite_eq_left rfl]
      rwa [heq] at hz'
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hzB' : z ∈ atomE E split X Δ (extendTrue δ') n :=
        atomE.succ_subset E split X Δ hΔ hEmne hsplit (extendTrue δ') n hz'
      have hempty := hdisj δ (extendTrue δ') ⟨j, hj, fun h => hjne (h.symm)⟩
      exact absurd (Set.mem_inter hzB hzB') (by rw [hempty]; simp)

namespace atomE

/-- **Closed form for `atomE`, generalizing `atomU_succ_eq`**: with `YseqE` in hand, `atomE`
satisfies exactly the same recursive description as `genAtom (YseqE E split X Δ) E.master`. -/
theorem succ_eq (δ : ℕ → Bool) (n : ℕ) :
    atomE E split X Δ δ (n + 1) =
      atomE E split X Δ δ n ∩
        (if δ n then YseqE E split X Δ n else E.master \ YseqE E split X Δ n) := by
  obtain ⟨hmatch, hmem, -⟩ := invariant E split X Δ hΔ hEmne hsplit n
  have hspec := hsplit (hmatch δ) (hmem δ) (X n)
  have hIeq := split_fst_eq_inter_YseqE E split X Δ hΔ hEmne hsplit δ n
  by_cases hδ : δ n = true
  · rw [succ, ite_eq_left hδ, ite_eq_left hδ]; exact hIeq
  · rw [succ, ite_eq_right hδ, ite_eq_right hδ]
    have hJeq : (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).2 =
        atomE E split X Δ δ n \ YseqE E split X Δ n := by
      have hunion := hspec.2.2.2.2.1
      have hinter := hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxB : x ∈ atomE E split X Δ δ n := hunion ▸ Or.inr hxJ
        refine ⟨hxB, fun hxY => ?_⟩
        have hxI : x ∈ (split (genAtom X Δ δ n) (atomE E split X Δ δ n) (X n)).1 :=
          hIeq ▸ Set.mem_inter hxB hxY
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxB, hxnY⟩
        rw [← hunion] at hxB
        rcases hxB with hxI | hxJ
        · exact absurd (hIeq ▸ hxI : x ∈ atomE E split X Δ δ n ∩ YseqE E split X Δ n).2 hxnY
        · exact hxJ
    rw [hJeq]
    have hsub := subset_master E split X Δ hΔ hEmne hsplit δ n
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

/-- **`atomE` coincides with the generic atom construction on `YseqE`/`E.master`**, generalizing
`atomU_eq_genAtom`. Lets every later argument treat `atomE` and `genAtom` uniformly (in particular,
`genAtom_forward`/`genAtom_self` — proved once, generically, in `Theorem88.lean` — apply verbatim
to the `E`-side atoms too). -/
theorem eq_genAtom (δ : ℕ → Bool) :
    ∀ n, atomE E split X Δ δ n = genAtom (YseqE E split X Δ) E.master δ n
  | 0 => rfl
  | (n + 1) => by
      rw [succ_eq E split X Δ hΔ hEmne hsplit, eq_genAtom δ n]; rfl

end atomE

/-- **The transfer lemma, generalized to `E`.** A finite Boolean combination of the `X i` is
non-empty in `D`'s carrier `Δ` iff the *same* Boolean combination of `YseqE E split X Δ i` is
non-empty in `E.master`. Mirrors `transfer_empty_iff`. -/
theorem transfer_empty_iffE {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n) :
    {x ∈ Δ | ∀ p ∈ cs, (p.2 = true ↔ x ∈ X p.1)}.Nonempty ↔
      {y ∈ E.master | ∀ p ∈ cs, (p.2 = true ↔ y ∈ YseqE E split X Δ p.1)}.Nonempty := by
  have hcore : ∀ δ n, genAtom X Δ δ n = ∅ ↔ genAtom (YseqE E split X Δ) E.master δ n = ∅ :=
    fun δ n => (atomE.invariant E split X Δ hΔ hEmne hsplit n).1 δ
      |>.trans (by rw [atomE.eq_genAtom E split X Δ hΔ hEmne hsplit])
  have hcore' : ∀ δ n, genAtom (YseqE E split X Δ) E.master δ n = ∅ ↔ genAtom X Δ δ n = ∅ :=
    fun δ n => (hcore δ n).symm
  exact ⟨transfer_dir X Δ (YseqE E split X Δ) E.master hcore hn,
    transfer_dir (YseqE E split X Δ) E.master X Δ hcore' hn⟩

end

end DomainTheory.NeighbourhoodSystems
