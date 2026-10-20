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
