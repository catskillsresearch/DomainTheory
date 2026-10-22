module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.branch_isTotal

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise113

set_option linter.unusedVariables false

theorem example_113 : ∀ (p : Nat → Bool),
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal DomainTheory.NeighbourhoodSystems.ExampleB.Str
    DomainTheory.NeighbourhoodSystems.ExampleB.B (DomainTheory.NeighbourhoodSystems.Exercise113.branch p) :=
  DomainTheory.NeighbourhoodSystems.Exercise113.branch_isTotal

end DomainTheory.NeighbourhoodSystems.Exercise113
