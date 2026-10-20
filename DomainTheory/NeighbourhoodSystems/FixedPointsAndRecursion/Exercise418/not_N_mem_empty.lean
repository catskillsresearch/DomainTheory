module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise418

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Example43

/-- `∅` is not a neighbourhood of `N`. -/
theorem not_N_mem_empty : ¬ N.mem (∅ : Set ℕ) := by
  rw [N_mem]
  rintro (h | ⟨n, h⟩)
  · exact Set.empty_ne_univ h
  · exact (Set.singleton_ne_empty n) h.symm

end DomainTheory.NeighbourhoodSystems.Exercise418
