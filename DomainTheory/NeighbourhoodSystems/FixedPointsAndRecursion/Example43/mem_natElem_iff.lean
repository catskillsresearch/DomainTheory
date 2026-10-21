/-ai
A neighbourhood belongs to the total element at n if and only if it is the whole space or the singleton of n.

The total element is unfolded and membership is rewritten as membership in the principal filter of that singleton. In the forward direction the neighbourhood is the whole space or a singleton, and in the singleton case the inclusion of the singleton of n forces the two elements to agree. In the reverse direction the whole space is a neighbourhood containing every set, and the singleton of n is a neighbourhood equal to itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


/-- A neighbourhood belongs to `n̂` iff it is `ℕ` (the master) or the singleton `{n}`. -/
theorem mem_natElem_iff {n : ℕ} {Y : Set ℕ} :
    (natElem n).mem Y ↔ Y = Set.univ ∨ Y = {n} := by
  unfold natElem
  rw [mem_principal]
  constructor
  · rintro ⟨hY, hsub⟩
    rcases hY with rfl | ⟨m, rfl⟩
    · exact Or.inl rfl
    · have hnm : n = m := Set.mem_singleton_iff.mp (Set.singleton_subset_iff.mp hsub)
      subst hnm; exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨memN_univ, Set.subset_univ _⟩
    · exact ⟨memN_singleton n, subset_rfl⟩

end DomainTheory.NeighbourhoodSystems.Example43
