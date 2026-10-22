module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise221.juxtapose_singleton_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise221

set_option linter.unusedVariables false

theorem example_221 : ∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str)
  (y :
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Exercise221.C)
  {Z : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str},
  Iff
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Exercise221.C
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap₂.toElementMap₂ DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Exercise221.C DomainTheory.NeighbourhoodSystems.Exercise221.C
        DomainTheory.NeighbourhoodSystems.Exercise221.C DomainTheory.NeighbourhoodSystems.Exercise221.juxtapose
        (DomainTheory.NeighbourhoodSystems.Exercise221.singletonElt σ) y)
      Z)
    (And
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Exercise221.C Z)
      (∃ (Y' : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        And
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise221.C y Y')
          (@LE.le (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (@Set.instLE DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (DomainTheory.NeighbourhoodSystems.ExampleB.prepend σ Y') Z))) :=
  DomainTheory.NeighbourhoodSystems.Exercise221.juxtapose_singleton_mem

end DomainTheory.NeighbourhoodSystems.Exercise221
