module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.FlatStem

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open DomainTheory.NeighbourhoodSystems.FlatStem
/-- Scott's Exercise 1.15: the flat and stem systems are not isomorphic. -/
theorem exercise_1_15 : ¬ (flat ≅ᴰ stem) :=
  not_isomorphic

