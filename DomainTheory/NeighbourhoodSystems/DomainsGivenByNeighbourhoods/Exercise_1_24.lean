module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem_more

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem
variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott's Exercise 1.24: every element is below some total element. -/
theorem exercise_1_24 (x : V.Element) : ∃ t, V.IsTotal t ∧ x ≤ t :=
  V.exists_total_ge x
