/-ai
The tail at zero is the set of all natural numbers.

Extensionality reduces the equality to an arbitrary natural number, and simplification with the definition of the tail discharges it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.tail

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

theorem tail_zero : tail 0 = Set.univ := by ext k; simp [tail]

end DomainTheory.NeighbourhoodSystems.Exercise425
