module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414

/-- Scott's hint operator `n·ℕ = {0} ∪ {n + m ∣ m ∈ n·ℕ}` on `P ℕ` (for fixed `n`). -/
def mulOp (n : ℕ) (u : Set ℕ) : Set ℕ := {0} ∪ {k | ∃ m ∈ u, k = n + m}

end DomainTheory.NeighbourhoodSystems.Exercise421
