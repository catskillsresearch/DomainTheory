/-ai
The successor image of a set of naturals is the set of numbers one greater than a member of the set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414

/-- Scott's `x⁺ = {n⁺ ∣ n ∈ x}` on `P ℕ`. -/
def succImage (x : Set ℕ) : Set ℕ := {k | ∃ j ∈ x, k = j + 1}

end DomainTheory.NeighbourhoodSystems.Exercise421
