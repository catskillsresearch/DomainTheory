/-ai
The filter of excluded points equal to the whole set of natural numbers is a total element of the cofinite system.

The numbered name example_116 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.ofExcluded_univ_isTotal

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Cofinite

set_option linter.unusedVariables false

theorem example_116 : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal Nat
  DomainTheory.NeighbourhoodSystems.Cofinite.cofiniteSystem
  (DomainTheory.NeighbourhoodSystems.Cofinite.ofExcluded (@Set.univ Nat)) :=
  DomainTheory.NeighbourhoodSystems.Cofinite.ofExcluded_univ_isTotal

end DomainTheory.NeighbourhoodSystems.Cofinite
