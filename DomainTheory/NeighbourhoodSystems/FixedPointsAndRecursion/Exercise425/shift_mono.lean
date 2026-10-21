/-ai
Shift preserves inclusion.

A successor witness in the smaller set is a successor witness in the larger set by the assumed inclusion.
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

theorem shift_mono {X X' : Set ℕ} (h : X' ⊆ X) : shift X' ⊆ shift X := by
  rintro k ⟨m, hm, rfl⟩; exact ⟨m, h hm, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise425
