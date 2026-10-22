module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.singleton_disjoint
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.stemMem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

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

end DomainTheory.NeighbourhoodSystems.Exercise115
