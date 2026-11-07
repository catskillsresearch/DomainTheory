module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.FinNonempty

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open DomainTheory.NeighbourhoodSystems.FinNonempty
/-- Scott's Exercise 1.14: singletons are total in the finite-nonempty system. -/
theorem exercise_1_14 : ∀ n : ℕ,
    neighborhoodSystem.IsTotal (neighborhoodSystem.principal (mem_singleton n)) :=
  singleton_isTotal

