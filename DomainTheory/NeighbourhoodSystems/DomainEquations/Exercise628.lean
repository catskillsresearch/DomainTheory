module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise628.isomorphic_of_finite_system
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise628.isomorphic_of_trianglelefteq_both

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_628.{u_1, u_2} : And
  (∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsFinite α D →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsFinite β E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E →
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq β α E D →
            @DomainTheory.NeighbourhoodSystems.Isomorphic α β D E)
  (∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    [Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)]
    [Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β E)],
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq β α E D → @DomainTheory.NeighbourhoodSystems.Isomorphic α β D E) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsFinite α D →
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsFinite β E →
        @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E →
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq β α E D →
            @DomainTheory.NeighbourhoodSystems.Isomorphic α β D E)
  (∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    [Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α D)]
    [Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β E)],
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq α β D E →
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq β α E D → @DomainTheory.NeighbourhoodSystems.Isomorphic α β D E)
  @DomainTheory.NeighbourhoodSystems.isomorphic_of_finite_system
  @DomainTheory.NeighbourhoodSystems.isomorphic_of_trianglelefteq_both

end DomainTheory.NeighbourhoodSystems
