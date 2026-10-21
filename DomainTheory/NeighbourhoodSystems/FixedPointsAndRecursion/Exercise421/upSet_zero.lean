/-ai
The up-set of zero is the set of all naturals.

Extend an arbitrary natural and simplify the defining inequality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise421.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414







/-- `[0] = ℕ`: the recursion base of 4.13(3). -/
theorem upSet_zero : upSet 0 = Set.univ := by
  ext k; simp [upSet]

end DomainTheory.NeighbourhoodSystems.Exercise421
