/-ai
The shift of the singleton of n is the singleton of n + 1.

A member of the shift is the successor of the unique element n, and n + 1 is the successor of n.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.shift
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- `1·{1ⁿ} = {1ⁿ⁺¹}`: shifting a singleton. -/
theorem shift_singleton (n : ℕ) : shift ({n} : Set ℕ) = {n + 1} := by
  ext k
  simp only [shift, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨n, rfl, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise425
