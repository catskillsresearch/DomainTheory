/-ai
Any two neighbourhoods of the binary-sequence system are nested or disjoint.

The proof cases on both neighbourhoods. Two cones are compared by the cone trichotomy. A singleton and a cone, in either order, are compared by the singleton-cone alternative, and in one order the empty intersection is rewritten by commutativity. Equal singletons coincide. Distinct singletons have empty intersection, because a common element would be both strings.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.singleton_cone_nd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

/-- Any two neighbourhoods of `C` are nested or disjoint. -/
theorem nestedOrDisjoint : NestedOrDisjoint memC := by
  rintro X Y (⟨σ, rfl⟩ | ⟨σ, rfl⟩) (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
  · exact cone_trichotomy σ τ
  · rcases singleton_cone_nd σ τ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases singleton_cone_nd τ σ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h : σ = τ
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl h2
      exact h h2

end DomainTheory.NeighbourhoodSystems.Example44
