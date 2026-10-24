module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise114
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/- concordance: source L456 EXERCISE 1.14 finite nonempty subsets -/
/-- **Exercise 1.14.** The neighbourhood system of finite non-empty subsets of `ℕ` (plus `Δ = ℕ`). -/
def neighborhoodSystem : NeighborhoodSystem ℕ where
  mem := mem
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    have hne : (X ∩ Y).Nonempty := (nonempty_of_mem hZ).mono hZsub
    rcases hX with hX | hX
    · rw [hX, Set.univ_inter]; exact hY
    · rcases hY with hY | hY
      · rw [hY, Set.inter_univ]; exact Or.inr hX
      · exact Or.inr ⟨hX.1.inter_of_left Y, hne⟩
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem ns_mem {X : Set ℕ} : neighborhoodSystem.mem X ↔ mem X := Iff.rfl

/-- `⊥ = ↑Δ = ↑ℕ`, the least element. -/
def bot : neighborhoodSystem.Element := neighborhoodSystem.bot

/-- The finite element `↑X` for a neighbourhood `X` (Scott's finite elements). -/
def fin {X : Set ℕ} (h : neighborhoodSystem.mem X) : neighborhoodSystem.Element :=
  neighborhoodSystem.principal h

theorem empty_not_mem : ¬ mem (∅ : Set ℕ) := by
  rintro (h | ⟨_, h⟩)
  · exact Set.empty_ne_univ h
  · exact Set.not_nonempty_empty h

theorem mem_singleton (n : ℕ) : mem {n} :=
  Or.inr ⟨Set.finite_singleton n, Set.singleton_nonempty n⟩

/-- **Exercise 1.14 (total elements).** The principal filter of a *singleton* `{n}` is a total
(maximal) element: any `y` it approximates approximates it back. (A `y ⊋ ↑{n}` would contain some
`W ∌ n`; then `{n} ∩ W = ∅ ∈ y ⊆ 𝒟`, impossible.) These are exactly the total elements. -/
theorem singleton_isTotal (n : ℕ) :
    neighborhoodSystem.IsTotal (neighborhoodSystem.principal (mem_singleton n)) := by
  intro y hy W hW
  have hn : y.mem {n} := hy {n} ⟨mem_singleton n, subset_rfl⟩
  refine ⟨y.sub hW, ?_⟩
  by_contra hc
  rw [Set.singleton_subset_iff] at hc
  have hempty : ({n} : Set ℕ) ∩ W = (∅ : Set ℕ) := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, hk⟩
    exact hc hk
  have hi := y.inter_mem hn hW
  rw [hempty] at hi
  exact empty_not_mem (y.sub hi)

section
set_option linter.unusedVariables false

theorem example_114 : ∀ (n : Nat),
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal Nat
    DomainTheory.NeighbourhoodSystems.Exercise114.neighborhoodSystem
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Nat
      DomainTheory.NeighbourhoodSystems.Exercise114.neighborhoodSystem
      (@Singleton.singleton Nat (Set Nat) (@Set.instSingletonSet Nat) n)
      (DomainTheory.NeighbourhoodSystems.Exercise114.mem_singleton n)) :=
  DomainTheory.NeighbourhoodSystems.Exercise114.singleton_isTotal
end
end

end DomainTheory.NeighbourhoodSystems.Exercise114
namespace DomainTheory.NeighbourhoodSystems.Exercise115
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Neighbourhoods of the flat domain: `Δ = ℕ` together with all singletons. -/
def flatMem (X : Set ℕ) : Prop := X = Set.univ ∨ ∃ n, X = {n}

/-- `{n} ∩ {m} = ∅` for `n ≠ m`. -/
theorem singleton_disjoint {n m : ℕ} (h : n ≠ m) : ({n} : Set ℕ) ∩ {m} = ∅ := by
  ext k
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨rfl, h2⟩
  exact h h2

theorem flatNOD : NestedOrDisjoint flatMem := by
  rintro X Y (rfl | ⟨n, rfl⟩) (rfl | ⟨m, rfl⟩)
  · exact Or.inl (subset_refl _)
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inl (Set.subset_univ _)
  · rcases eq_or_ne n m with rfl | h
    · exact Or.inl (subset_refl _)
    · exact Or.inr (Or.inr (singleton_disjoint h))

/-- **Exercise 1.15 — the flat domain.** `𝒟 = {ℕ} ∪ {{n}}`. -/
def flat : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint flatMem Set.univ Set.univ_nonempty
    (Or.inl rfl) flatNOD (fun _ => Set.subset_univ _)

@[simp] theorem flat_mem {X : Set ℕ} : flat.mem X ↔ X = Set.univ ∨ ∃ n, X = {n} := Iff.rfl

@[simp] theorem flat_master : flat.master = Set.univ := rfl

/-- Neighbourhoods of the stem domain: `Δ = ℕ`, the pair `{0,1}`, and all singletons. -/
def stemMem (X : Set ℕ) : Prop := X = Set.univ ∨ X = {0, 1} ∨ ∃ n, X = {n}

theorem stemNOD : NestedOrDisjoint stemMem := by
  have pair_single : ∀ m : ℕ, ({m} : Set ℕ) ⊆ {0, 1} ∨ ({0, 1} : Set ℕ) ∩ {m} = ∅ := by
    intro m
    by_cases h : m = 0 ∨ m = 1
    · refine Or.inl ?_
      rcases h with rfl | rfl <;> intro k hk <;> simp_all
    · refine Or.inr ?_
      ext k
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro (rfl | rfl) rfl <;> simp_all
  rintro X Y (rfl | rfl | ⟨n, rfl⟩) (rfl | rfl | ⟨m, rfl⟩)
  · exact Or.inl (subset_refl _)
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inl (Set.subset_univ _)
  · exact Or.inl (subset_refl _)
  · rcases pair_single m with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (Set.subset_univ _)
  · rcases pair_single n with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases eq_or_ne n m with rfl | h
    · exact Or.inl (subset_refl _)
    · exact Or.inr (Or.inr (singleton_disjoint h))

/-- **Exercise 1.15 — the stem domain.** `𝒟 = {ℕ, {0,1}} ∪ {{n}}`. -/
def stem : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint stemMem Set.univ Set.univ_nonempty
    (Or.inl rfl) stemNOD (fun _ => Set.subset_univ _)

@[simp] theorem stem_mem {X : Set ℕ} :
    stem.mem X ↔ X = Set.univ ∨ X = {0, 1} ∨ ∃ n, X = {n} := Iff.rfl

theorem flat_empty_not_mem : ¬ flat.mem (∅ : Set ℕ) := by
  rintro (h | ⟨n, h⟩)
  · exact Set.empty_ne_univ h
  · exact absurd h.symm (Set.singleton_ne_empty n)

/-- The atom `↑{n}` (a finite element). -/
theorem flat_mem_singleton (n : ℕ) : flat.mem {n} := Or.inr ⟨n, rfl⟩

/-- **Flat classification.** Every element is `⊥` or an atom `↑{n}`. *Classical.* -/
theorem flat_classify (x : flat.Element) :
    x = flat.bot ∨ ∃ n, x = flat.principal (flat_mem_singleton n) := by
  classical
  by_cases h : ∃ n, x.mem {n}
  · obtain ⟨n, hn⟩ := h
    refine Or.inr ⟨n, ?_⟩
    have huniq : ∀ m, x.mem {m} → m = n := by
      intro m hm
      by_contra hmn
      have hi : x.mem (({m} : Set ℕ) ∩ {n}) := x.inter_mem hm hn
      rw [singleton_disjoint hmn] at hi
      exact flat_empty_not_mem (x.sub hi)
    apply Element.ext
    intro W
    constructor
    · intro hx
      rcases (x.sub hx) with rfl | ⟨k, rfl⟩
      · exact ⟨Or.inl rfl, Set.subset_univ _⟩
      · obtain rfl := huniq k hx
        exact ⟨flat_mem_singleton k, subset_rfl⟩
    · rintro ⟨hWmem, hsub⟩
      exact x.up_mem hn hWmem hsub
  · refine Or.inl ?_
    apply Element.ext
    intro W
    rw [flat.mem_bot]
    constructor
    · intro hx
      rcases (x.sub hx) with rfl | ⟨k, rfl⟩
      · rfl
      · exact absurd ⟨k, hx⟩ h
    · rintro rfl
      exact x.master_mem

/-- **All elements of `flat` are finite** (principal). -/
theorem flat_all_finite (x : flat.Element) : ∃ (X : Set ℕ) (h : flat.mem X), x = flat.principal h := by
  rcases flat_classify x with rfl | ⟨n, rfl⟩
  · exact ⟨flat.master, flat.master_mem, rfl⟩
  · exact ⟨{n}, flat_mem_singleton n, rfl⟩

/-- **Flat: every atom is maximal (total).** -/
theorem flat_atom_maximal (n : ℕ) (y : flat.Element)
    (hle : flat.principal (flat_mem_singleton n) ≤ y) :
    y = flat.principal (flat_mem_singleton n) := by
  rcases flat_classify y with rfl | ⟨m, rfl⟩
  · exfalso
    have hmem : flat.bot.mem {n} := hle {n} ⟨flat_mem_singleton n, subset_rfl⟩
    rw [flat.mem_bot, flat_master] at hmem
    have : (n + 1) ∈ ({n} : Set ℕ) := by rw [hmem]; exact Set.mem_univ _
    simp at this
  · have hsub : ({m} : Set ℕ) ⊆ {n} :=
      (flat.principal_le_iff (flat_mem_singleton n) (flat_mem_singleton m)).mp hle
    obtain rfl : m = n := Set.mem_singleton_iff.mp (Set.singleton_subset_iff.mp hsub)
    rfl

/-- `flat` is infinite: the atoms `↑{n}` are pairwise distinct. -/
theorem flat_infinite : Function.Injective (fun n => flat.principal (flat_mem_singleton n)) := by
  intro n m h
  have := flat.principal_injective (flat_mem_singleton n) (flat_mem_singleton m) h
  exact Set.singleton_injective this

/-- **Flat has no strict 3-chain** (`a ⊏ b ⊏ c` is impossible): `⊥` is least and atoms are maximal. -/
theorem flat_no_three_chain : ¬ ∃ a b c : flat.Element, a < b ∧ b < c := by
  rintro ⟨a, b, c, hab, hbc⟩
  rcases flat_classify b with rfl | ⟨n, rfl⟩
  · exact absurd (le_antisymm hab.le (flat.bot_le a)) (ne_of_lt hab)
  · exact (ne_of_lt hbc) (flat_atom_maximal n c hbc.le).symm

/-- **Flat has no infinite ascending chain.** -/
theorem flat_no_infinite_chain : ¬ ∃ f : ℕ → flat.Element, StrictMono f := by
  rintro ⟨f, hf⟩
  exact flat_no_three_chain
    ⟨f 0, f 1, f 2, hf (by norm_num), hf (by norm_num)⟩

theorem stem_mem_pair : stem.mem {0, 1} := Or.inr (Or.inl rfl)

theorem stem_mem_univ : stem.mem Set.univ := Or.inl rfl

theorem stem_mem_zero : stem.mem {0} := Or.inr (Or.inr ⟨0, rfl⟩)

/-- A strict step between principal filters of `stem`: `Y ⊊ X` (proper) gives `↑X ⊏ ↑Y`. -/
theorem stem_principal_lt {X Y : Set ℕ} (hX : stem.mem X) (hY : stem.mem Y)
    (hYX : Y ⊆ X) (hne : X ≠ Y) : stem.principal hX < stem.principal hY := by
  rw [lt_iff_le_and_ne]
  refine ⟨(stem.principal_le_iff hX hY).mpr hYX, ?_⟩
  intro he
  exact hne (stem.principal_injective hX hY he)

/-- **Stem contains a strict 3-chain** `⊥ = ↑ℕ ⊏ ↑{0,1} ⊏ ↑{0}` — the structural feature that
distinguishes it from `flat`. -/
theorem stem_three_chain : ∃ a b c : stem.Element, a < b ∧ b < c := by
  refine ⟨stem.principal stem_mem_univ, stem.principal stem_mem_pair,
    stem.principal stem_mem_zero, ?_, ?_⟩
  · refine stem_principal_lt stem_mem_univ stem_mem_pair (Set.subset_univ _) ?_
    intro h
    have : (2 : ℕ) ∈ ({0, 1} : Set ℕ) := h ▸ Set.mem_univ 2
    simp at this
  · refine stem_principal_lt stem_mem_pair stem_mem_zero
      (Set.singleton_subset_iff.mpr (by simp)) ?_
    intro h
    have : (1 : ℕ) ∈ ({0} : Set ℕ) := h ▸ (by simp : (1 : ℕ) ∈ ({0, 1} : Set ℕ))
    simp at this
end

end DomainTheory.NeighbourhoodSystems.Exercise115
end
