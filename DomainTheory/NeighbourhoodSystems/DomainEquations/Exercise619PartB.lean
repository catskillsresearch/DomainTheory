module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB.prodTok_subsystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise619

set_option linter.unusedVariables false

theorem example_619_part_b : ∀ {A₀ A₁ B₀ B₁ : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
  @DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str A₀.sys B₀.sys →
    @DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str A₁.sys B₁.sys →
      @DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str (A₀.prod A₁).sys
        (B₀.prod B₁).sys :=
  @DomainTheory.NeighbourhoodSystems.Exercise619.prodTok_subsystem

end DomainTheory.NeighbourhoodSystems.Exercise619
