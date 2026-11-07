module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Cofinite

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open DomainTheory.NeighbourhoodSystems.Cofinite
/-- Scott's Exercise 1.16: the cofinite system has a total element (exclude nothing). -/
theorem exercise_1_16 : cofiniteSystem.IsTotal (ofExcluded Set.univ) :=
  ofExcluded_univ_isTotal

