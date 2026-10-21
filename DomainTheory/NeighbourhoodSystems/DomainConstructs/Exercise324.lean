/-ai
The function space into a product is isomorphic, as a domain, to the product of the two function spaces.

The numbered name example_324 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324.funProd_isomorphic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_324.{u_1, u_2, u_3} : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ},
  @DomainTheory.NeighbourhoodSystems.Isomorphic
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α (Sum β γ) V₀
      (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
    (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂))
    (@DomainTheory.NeighbourhoodSystems.funSpace α (Sum β γ) V₀ (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
    (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)) :=
  @DomainTheory.NeighbourhoodSystems.funProd_isomorphic

end DomainTheory.NeighbourhoodSystems
