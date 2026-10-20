module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414

/-- The relation `≤` itself, as a subset of `ℕ × ℕ`. -/
def leRel : Set (ℕ × ℕ) := {p | p.1 ≤ p.2}

end DomainTheory.NeighbourhoodSystems.Exercise421
