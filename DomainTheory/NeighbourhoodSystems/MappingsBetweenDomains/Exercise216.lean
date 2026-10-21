/-ai
An approximable map from the binary-string domain into the truth-value domain that satisfies the three parity equations equals the parity map. The element map of the prefixing map of a finite string is Scott's prefixing operation on elements.

The numbered name example_216 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise216.eq_parityMap_of_satisfies
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise216.toElementMap_sigmaMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise216

set_option linter.unusedVariables false

theorem example_216 : And
  (∀
    {g :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.Example23.T},
    DomainTheory.NeighbourhoodSystems.Exercise216.SatisfiesParityEquations g →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.Example23.T)
        g DomainTheory.NeighbourhoodSystems.Example23.parityMap)
  (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str)
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B (DomainTheory.NeighbourhoodSystems.Exercise216.sigmaMap σ) x)
      (DomainTheory.NeighbourhoodSystems.ExampleB.sigmaElt σ x)) :=
  @And.intro
  (∀
    {g :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.Example23.T},
    DomainTheory.NeighbourhoodSystems.Exercise216.SatisfiesParityEquations g →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.Example23.T)
        g DomainTheory.NeighbourhoodSystems.Example23.parityMap)
  (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str)
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B (DomainTheory.NeighbourhoodSystems.Exercise216.sigmaMap σ) x)
      (DomainTheory.NeighbourhoodSystems.ExampleB.sigmaElt σ x))
  (@DomainTheory.NeighbourhoodSystems.Exercise216.eq_parityMap_of_satisfies)
  DomainTheory.NeighbourhoodSystems.Exercise216.toElementMap_sigmaMap

end DomainTheory.NeighbourhoodSystems.Exercise216
