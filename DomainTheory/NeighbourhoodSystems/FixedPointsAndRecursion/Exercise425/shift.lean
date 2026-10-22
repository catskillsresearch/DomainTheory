/-ai
The shift of a set of naturals is the set of successors of its members.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- Shifting a set up by one length: `shift X = {m + 1 ∣ m ∈ X}` (the token action of prepending a
`1`). -/
def shift (X : Set ℕ) : Set ℕ := {k | ∃ m ∈ X, k = m + 1}

end DomainTheory.NeighbourhoodSystems.Exercise425
