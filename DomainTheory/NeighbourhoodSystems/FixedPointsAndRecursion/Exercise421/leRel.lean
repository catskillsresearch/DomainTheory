/-ai
The order relation on the naturals, viewed as a subset of pairs, consists of those pairs whose first component is at most the second.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414

/-- The relation `≤` itself, as a subset of `ℕ × ℕ`. -/
def leRel : Set (ℕ × ℕ) := {p | p.1 ≤ p.2}

end DomainTheory.NeighbourhoodSystems.Exercise421
