module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.singleton_tail_nd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- Any two neighbourhoods of `C₁` are nested or disjoint. -/
theorem nestedOrDisjoint : NestedOrDisjoint memC1 := by
  rintro X Y (⟨n, rfl⟩ | ⟨n, rfl⟩) (⟨m, rfl⟩ | ⟨m, rfl⟩)
  · rcases le_total n m with h | h
    · exact Or.inr (Or.inl (fun k hk => le_trans h hk))
    · exact Or.inl (fun k hk => le_trans h hk)
  · rcases singleton_tail_nd n m with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases singleton_tail_nd m n with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases h : n = m
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl h2; exact h h2

end DomainTheory.NeighbourhoodSystems.Exercise425
