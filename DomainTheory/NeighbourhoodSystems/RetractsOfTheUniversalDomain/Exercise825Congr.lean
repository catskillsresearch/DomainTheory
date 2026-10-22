module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.curry_isomorphic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_825_congr.{u_1, u_2, u_3} : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
  (V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ),
  @DomainTheory.NeighbourhoodSystems.Isomorphic
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      V₂)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
      V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
    (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)) :=
  @DomainTheory.NeighbourhoodSystems.curry_isomorphic

end DomainTheory.NeighbourhoodSystems
