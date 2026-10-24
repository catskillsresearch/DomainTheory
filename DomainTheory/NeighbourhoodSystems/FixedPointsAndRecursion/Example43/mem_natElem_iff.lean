module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.natElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroElt
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.constLiftN
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.succMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.predVal
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.predMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroVal
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.univ_ne_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.singleton_ne_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.singleton_nat_inj
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.T

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
