module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₀_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₁_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.diagC_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.swapC_apply

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- The uncurried `(f, g), x ↦ ⟨f(x), g(x)⟩` over `((𝒟₂→𝒟₀) × (𝒟₂→𝒟₁)) × 𝒟₂ → 𝒟₀ × 𝒟₁`. -/
def funpairMapTbl (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂) (prod V₀ V₁) :=
  paired
    ((evalMap V₂ V₀).comp
      (paired
        ((proj₀ (funSpace V₂ V₀) (funSpace V₂ V₁)).comp
          (proj₀ (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂))
        (proj₁ (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂)))
    ((evalMap V₂ V₁).comp
      (paired
        ((proj₁ (funSpace V₂ V₀) (funSpace V₂ V₁)).comp
          (proj₀ (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂))
        (proj₁ (prod (funSpace V₂ V₀) (funSpace V₂ V₁)) V₂)))

end DomainTheory.NeighbourhoodSystems
