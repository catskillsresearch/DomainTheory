module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.natElem_injective

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise418

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Example43


/-- **Exercise 4.18 (Scott 1981, PRG-19).** `0̂` is not a numeral successor. -/
theorem natElem_zero_ne_succ (k : ℕ) : natElem 0 ≠ natElem (k + 1) := fun h =>
  Nat.succ_ne_zero k (natElem_injective h).symm

end DomainTheory.NeighbourhoodSystems.Exercise418
