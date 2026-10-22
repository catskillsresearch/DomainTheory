/-ai
The up-set of a natural m is the set of naturals at least m, the value of Scott's unique function of exercise 4.13(3).
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414

/-- The up-set `[m] = {k ∣ m ≤ k}` — the value of Scott's unique function `[·]` of 4.13(3). -/
def upSet (m : ℕ) : Set ℕ := {k | m ≤ k}

end DomainTheory.NeighbourhoodSystems.Exercise421
