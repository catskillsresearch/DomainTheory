/-ai
The singletons of two finite binary strings are nested or disjoint.

If the two strings are equal, the singletons coincide. If they are not, the intersection is empty, because a common element would force the two strings to be equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Nested-or-disjoint for two terminator singletons: equal or disjoint. -/
theorem singleton_singleton_nd (σ τ : Str) :
    ({σ} : Set Str) ⊆ ({τ} : Set Str) ∨ ({τ} : Set Str) ⊆ ({σ} : Set Str) ∨
      ({σ} : Set Str) ∩ ({τ} : Set Str) = ∅ := by
  by_cases h : σ = τ
  · subst h; exact Or.inl subset_rfl
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
      not_and]
    rintro rfl h2
    exact h h2

end DomainTheory.NeighbourhoodSystems.Exercise221
