/-ai
Any two neighbourhoods of the natural-number system are nested or disjoint.

The proof cases on both neighbourhoods. Two copies of the whole space are equal. The whole space contains a singleton, and a singleton is contained in the whole space. Equal singletons coincide. Distinct singletons have empty intersection, because a common element would be both indices.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- Any two neighbourhoods of `N` are nested or disjoint: `ℕ` contains every singleton, and two
distinct singletons are disjoint. -/
theorem nestedOrDisjoint : NestedOrDisjoint memN := by
  rintro X Y (rfl | ⟨n, rfl⟩) (rfl | ⟨m, rfl⟩)
  · exact Or.inl (Set.Subset.refl _)
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inl (Set.subset_univ _)
  · by_cases h : n = m
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext k
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl hkm
      exact h hkm

end DomainTheory.NeighbourhoodSystems.Example43
