module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.exercise_8_20
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.D_trianglelefteq_funSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.D_trianglelefteq_prod

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_820.{u} : And
  (And
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      And
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq α (Sum α α) D
          (@DomainTheory.NeighbourhoodSystems.prod α α D D))
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
          (@DomainTheory.NeighbourhoodSystems.funSpace α α D D)))
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq α (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
        (@DomainTheory.NeighbourhoodSystems.funSpace α α D D)))
  (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq α (Sum α α) D (@DomainTheory.NeighbourhoodSystems.prod α α D D)) :=
  @And.intro
  (And
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      And
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq α (Sum α α) D
          (@DomainTheory.NeighbourhoodSystems.prod α α D D))
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
          (@DomainTheory.NeighbourhoodSystems.funSpace α α D D)))
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq α (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
        (@DomainTheory.NeighbourhoodSystems.funSpace α α D D)))
  (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq α (Sum α α) D (@DomainTheory.NeighbourhoodSystems.prod α α D D))
  (@And.intro
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      And
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq α (Sum α α) D
          (@DomainTheory.NeighbourhoodSystems.prod α α D D))
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
          (@DomainTheory.NeighbourhoodSystems.funSpace α α D D)))
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq α (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
        (@DomainTheory.NeighbourhoodSystems.funSpace α α D D))
    @DomainTheory.NeighbourhoodSystems.exercise_8_20 @DomainTheory.NeighbourhoodSystems.D_trianglelefteq_funSpace)
  @DomainTheory.NeighbourhoodSystems.D_trianglelefteq_prod

end DomainTheory.NeighbourhoodSystems
