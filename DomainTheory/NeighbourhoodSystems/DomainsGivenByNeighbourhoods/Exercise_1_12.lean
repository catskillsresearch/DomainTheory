module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.TailNat

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open DomainTheory.NeighbourhoodSystems.TailNat
/-- Scott's Exercise 1.12: final segments of ℕ form a neighbourhood system whose
    only total element is the limit top. -/
theorem exercise_1_12 :
    (NestedOrDisjoint mem ∧
      ∀ x : neighborhoodSystem.Element, neighborhoodSystem.IsTotal x ↔ x = top) :=
  ⟨nestedOrDisjoint, isTotal_iff_top⟩

