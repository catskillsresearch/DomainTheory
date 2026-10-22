module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.isStrict_prodMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

end Exercise618

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems.Exercise618

set_option linter.unusedVariables false

theorem example_618.{u_2, u_3, u_4, u_5} : ∀ {α : Type u_2} {β : Type u_3} {α' : Type u_4} {β' : Type u_5}
  {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  {V₀' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α'}
  {V₁' : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β'}
  {f₀ : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α' V₀ V₀'}
  {f₁ : @DomainTheory.NeighbourhoodSystems.ApproximableMap β β' V₁ V₁'},
  @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict α α' V₀ V₀' f₀ →
    @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict β β' V₁ V₁' f₁ →
      @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict (Sum α β) (Sum α' β')
        (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.prod α' β' V₀' V₁')
        (@DomainTheory.NeighbourhoodSystems.prodMap α β α' β' V₀ V₁ V₀' V₁' f₀ f₁) :=
  @DomainTheory.NeighbourhoodSystems.Exercise618.isStrict_prodMap

end DomainTheory.NeighbourhoodSystems.Exercise618
