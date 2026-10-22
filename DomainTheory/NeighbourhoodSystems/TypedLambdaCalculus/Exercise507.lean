module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise507.uncurry_lam_two_vars

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise507

set_option linter.unusedVariables false

theorem example_507.{u_1, u_2, u_5} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β} {α_1 : Type u_5}
  {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α_1}
  (g :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1 (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      V₂),
  @Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) α_1
      (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
    (@DomainTheory.NeighbourhoodSystems.uncurry α β α_1 V₀ V₁ V₂
      (@DomainTheory.NeighbourhoodSystems.curry α β α_1 V₀ V₁ V₂ g))
    g :=
  @DomainTheory.NeighbourhoodSystems.Exercise507.uncurry_lam_two_vars

end DomainTheory.NeighbourhoodSystems.Exercise507
