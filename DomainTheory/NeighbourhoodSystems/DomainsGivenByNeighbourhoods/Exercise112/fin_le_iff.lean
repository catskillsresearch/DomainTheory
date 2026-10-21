/-ai
One finite element of the final-segment system approximates another if and only if the first index is at most the second.

Unfold the finite elements, rewrite the order of principal filters as inclusion of tails, and rewrite that inclusion as the numerical comparison.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem












/-- The finite elements form an ascending chain: `fin n ⊑ fin m ↔ n ≤ m`. -/
theorem fin_le_iff (n m : ℕ) : fin n ≤ fin m ↔ n ≤ m := by
  rw [fin, fin, neighborhoodSystem.principal_le_iff, tail_subset_iff]

end DomainTheory.NeighbourhoodSystems.Exercise112
