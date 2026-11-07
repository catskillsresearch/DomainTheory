module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.PositiveDiff

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open DomainTheory.NeighbourhoodSystems.PositiveDiff
/-- Scott's Exercise 1.19: a counterexample that is not positive, and a positive example. -/
theorem exercise_1_19 :
    ¬ notPositiveSystem.IsPositive ∧ positiveExample.IsPositive :=
  ⟨not_isPositive, positiveExample_isPositive⟩
