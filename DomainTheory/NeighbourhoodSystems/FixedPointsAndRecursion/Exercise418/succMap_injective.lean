module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.natElem_injective

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise418

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Example43


/-- **Exercise 4.18 (Scott 1981, PRG-19).** `succ` is injective on the total elements. -/
theorem succMap_injective {n m : ℕ}
    (h : succMap.toElementMap (natElem n) = succMap.toElementMap (natElem m)) : n = m := by
  rw [succMap_natElem, succMap_natElem] at h
  have := natElem_injective h
  omega

end DomainTheory.NeighbourhoodSystems.Exercise418
