module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise114.singleton_isTotal

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise114

set_option linter.unusedVariables false

theorem example_114 : ∀ (n : Nat),
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal Nat
    DomainTheory.NeighbourhoodSystems.Exercise114.neighborhoodSystem
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Nat
      DomainTheory.NeighbourhoodSystems.Exercise114.neighborhoodSystem
      (@Singleton.singleton Nat (Set Nat) (@Set.instSingletonSet Nat) n)
      (DomainTheory.NeighbourhoodSystems.Exercise114.mem_singleton n)) :=
  DomainTheory.NeighbourhoodSystems.Exercise114.singleton_isTotal

end DomainTheory.NeighbourhoodSystems.Exercise114
