module

import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_7
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_4

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise115
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

def flatMem (X : Set ℕ) : Prop := X = Set.univ ∨ ∃ n, X = {n}

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

def flat : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint flatMem Set.univ Set.univ_nonempty
    (Or.inl rfl) flatNOD (fun _ => Set.subset_univ _)

@[simp] theorem flat_mem {X : Set ℕ} : flat.mem X ↔ X = Set.univ ∨ ∃ n, X = {n} := Iff.rfl

@[simp] theorem flat_master : flat.master = Set.univ := rfl

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

def stem : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint stemMem Set.univ Set.univ_nonempty
    (Or.inl rfl) stemNOD (fun _ => Set.subset_univ _)

@[simp] theorem stem_mem {X : Set ℕ} :
    stem.mem X ↔ X = Set.univ ∨ X = {0, 1} ∨ ∃ n, X = {n} := Iff.rfl

theorem flat_empty_not_mem : ¬ flat.mem (∅ : Set ℕ) := by
  rintro (h | ⟨n, h⟩)
  · exact Set.empty_ne_univ h
  · exact absurd h.symm (Set.singleton_ne_empty n)

theorem flat_mem_singleton (n : ℕ) : flat.mem {n} := Or.inr ⟨n, rfl⟩

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

theorem flat_all_finite (x : flat.Element) : ∃ (X : Set ℕ) (h : flat.mem X), x = flat.principal h := by
  rcases flat_classify x with rfl | ⟨n, rfl⟩
  · exact ⟨flat.master, flat.master_mem, rfl⟩
  · exact ⟨{n}, flat_mem_singleton n, rfl⟩

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

theorem flat_infinite : Function.Injective (fun n => flat.principal (flat_mem_singleton n)) := by
  intro n m h
  have := flat.principal_injective (flat_mem_singleton n) (flat_mem_singleton m) h
  exact Set.singleton_injective this

theorem flat_no_three_chain : ¬ ∃ a b c : flat.Element, a < b ∧ b < c := by
  rintro ⟨a, b, c, hab, hbc⟩
  rcases flat_classify b with rfl | ⟨n, rfl⟩
  · exact absurd (le_antisymm hab.le (flat.bot_le a)) (ne_of_lt hab)
  · exact (ne_of_lt hbc) (flat_atom_maximal n c hbc.le).symm

theorem flat_no_infinite_chain : ¬ ∃ f : ℕ → flat.Element, StrictMono f := by
  rintro ⟨f, hf⟩
  exact flat_no_three_chain
    ⟨f 0, f 1, f 2, hf (by norm_num), hf (by norm_num)⟩

theorem stem_mem_pair : stem.mem {0, 1} := Or.inr (Or.inl rfl)

theorem stem_mem_univ : stem.mem Set.univ := Or.inl rfl

theorem stem_mem_zero : stem.mem {0} := Or.inr (Or.inr ⟨0, rfl⟩)

theorem stem_principal_lt {X Y : Set ℕ} (hX : stem.mem X) (hY : stem.mem Y)
    (hYX : Y ⊆ X) (hne : X ≠ Y) : stem.principal hX < stem.principal hY := by
  rw [lt_iff_le_and_ne]
  refine ⟨(stem.principal_le_iff hX hY).mpr hYX, ?_⟩
  intro he
  exact hne (stem.principal_injective hX hY he)

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

namespace DomainTheory.NeighbourhoodSystems.Exercise115
section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem not_isomorphic : ¬ (flat ≅ᴰ stem) := by
  rintro ⟨e⟩
  obtain ⟨a, b, c, hab, hbc⟩ := stem_three_chain
  exact flat_no_three_chain
    ⟨e.symm a, e.symm b, e.symm c, e.symm.lt_iff_lt.mpr hab, e.symm.lt_iff_lt.mpr hbc⟩

section
set_option linter.unusedVariables false

theorem example_115 : Not
  (@DomainTheory.NeighbourhoodSystems.Isomorphic Nat Nat DomainTheory.NeighbourhoodSystems.Exercise115.flat
    DomainTheory.NeighbourhoodSystems.Exercise115.stem) :=
  DomainTheory.NeighbourhoodSystems.Exercise115.not_isomorphic
end
end

end DomainTheory.NeighbourhoodSystems.Exercise115
end
