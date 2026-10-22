module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise418

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Example43

/-- Distinct singletons are disjoint. -/
theorem singleton_inter_eq_empty {n m : ℕ} (hmn : m ≠ n) :
    ({n} : Set ℕ) ∩ {m} = ∅ := by
  ext k
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl h2
  exact hmn h2.symm
end DomainTheory.NeighbourhoodSystems.Exercise418
