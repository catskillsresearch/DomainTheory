/-ai
The flat domain and the stem domain are not isomorphic as domains.

The numbered name example_115 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.not_isomorphic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise115

set_option linter.unusedVariables false

theorem example_115 : Not
  (@DomainTheory.NeighbourhoodSystems.Isomorphic Nat Nat DomainTheory.NeighbourhoodSystems.Exercise115.flat
    DomainTheory.NeighbourhoodSystems.Exercise115.stem) :=
  DomainTheory.NeighbourhoodSystems.Exercise115.not_isomorphic

end DomainTheory.NeighbourhoodSystems.Exercise115
