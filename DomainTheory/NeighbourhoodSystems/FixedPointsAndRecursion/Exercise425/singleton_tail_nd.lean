/-ai
A singleton and a tail are nested or disjoint.

If the tail starts at or before the element of the singleton, that singleton is contained in the tail. Otherwise their intersection is empty, because a common element would be the element of the singleton and would lie at or after the start of the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- A singleton and a tail are nested or disjoint. -/
theorem singleton_tail_nd (n k : ℕ) :
    ({k} : Set ℕ) ⊆ tail n ∨ tail n ⊆ {k} ∨ ({k} : Set ℕ) ∩ tail n = ∅ := by
  by_cases h : n ≤ k
  · exact Or.inl (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact h)
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_tail, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl hw; exact h hw

end DomainTheory.NeighbourhoodSystems.Exercise425
