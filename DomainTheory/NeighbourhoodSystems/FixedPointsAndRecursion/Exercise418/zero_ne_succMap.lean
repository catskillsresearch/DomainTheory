/-ai
The numeral zero is not the successor of any numeral.

The successor of a numeral is the numeral of the successor, and that numeral is distinct from the numeral zero.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise418.natElem_zero_ne_succ

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise418

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Example43


/-- **Exercise 4.18 (Scott 1981, PRG-19).** `0̂` is not in the image of `succ` — Peano's
"zero is not a successor". -/
theorem zero_ne_succMap (n : ℕ) : natElem 0 ≠ succMap.toElementMap (natElem n) := by
  rw [succMap_natElem]
  exact natElem_zero_ne_succ n

end DomainTheory.NeighbourhoodSystems.Exercise418
