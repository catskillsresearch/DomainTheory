module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.prodTok_iso_prod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok_iso_sum

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise619

set_option linter.unusedVariables false

theorem example_619 : And
  (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)
      (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀ D₁))
  (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
    {h₀ :
      ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀ X →
          @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
    {h₁ :
      ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₁ Y →
          @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Option (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str))
      (DomainTheory.NeighbourhoodSystems.Exercise619.sumTok D₀ D₁ h₀ h₁)
      (@DomainTheory.NeighbourhoodSystems.sum DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀ D₁ h₀ h₁)) :=
  @And.intro
  (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)
      (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀ D₁))
  (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
    {h₀ :
      ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀ X →
          @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
    {h₁ :
      ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₁ Y →
          @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Option (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str))
      (DomainTheory.NeighbourhoodSystems.Exercise619.sumTok D₀ D₁ h₀ h₁)
      (@DomainTheory.NeighbourhoodSystems.sum DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀ D₁ h₀ h₁))
  @DomainTheory.NeighbourhoodSystems.Exercise619.prodTok_iso_prod
  @DomainTheory.NeighbourhoodSystems.Exercise619.sumTok_iso_sum

end DomainTheory.NeighbourhoodSystems.Exercise619
