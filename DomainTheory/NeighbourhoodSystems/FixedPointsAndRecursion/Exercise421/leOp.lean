/-ai
Scott's operator on subsets of pairs of naturals sends a set to the diagonal pairs, together with the pairs whose second component is one more than the second component of a pair already in the set with the same first component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise421

open DomainTheory.NeighbourhoodSystems.Exercise414

/-- Scott's operator `ℓ ↦ {(n, n)} ∪ {(n, m⁺) ∣ (n, m) ∈ ℓ}` on `P(ℕ × ℕ)`. -/
def leOp (u : Set (ℕ × ℕ)) : Set (ℕ × ℕ) :=
  {p | p.1 = p.2} ∪ {p | ∃ m, (p.1, m) ∈ u ∧ p.2 = m + 1}

end DomainTheory.NeighbourhoodSystems.Exercise421
