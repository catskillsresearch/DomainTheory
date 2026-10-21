/-ai
The tail of length n is the set of naturals at least n.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- The tail `tail n = {1ᵐ ∣ m ≥ n} = {m ∣ n ≤ m}` (the partial information "at least `n` ones"). -/
def tail (n : ℕ) : Set ℕ := {m | n ≤ m}

end DomainTheory.NeighbourhoodSystems.Exercise425
