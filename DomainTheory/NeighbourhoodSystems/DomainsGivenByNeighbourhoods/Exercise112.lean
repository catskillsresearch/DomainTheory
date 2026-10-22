module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.element_eq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise112

set_option linter.unusedVariables false

theorem example_112 : ∀
  (x :
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
      DomainTheory.NeighbourhoodSystems.Exercise112.neighborhoodSystem),
  Or
    (∃ (n : Nat),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
          DomainTheory.NeighbourhoodSystems.Exercise112.neighborhoodSystem)
        x (DomainTheory.NeighbourhoodSystems.Exercise112.fin n))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
        DomainTheory.NeighbourhoodSystems.Exercise112.neighborhoodSystem)
      x DomainTheory.NeighbourhoodSystems.Exercise112.top) :=
  DomainTheory.NeighbourhoodSystems.Exercise112.element_eq

end DomainTheory.NeighbourhoodSystems.Exercise112
