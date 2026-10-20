module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₀_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₁_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.diagC_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.swapC_apply

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- The uncurried `(g, f), x ↦ g(f(x))` over `((𝒟₁→𝒟₂) × (𝒟₀→𝒟₁)) × 𝒟₀ → 𝒟₂`, built purely from
projections, pairing and `eval` (this is the variable-free expression Scott alludes to). -/
def compMapTbl (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀) V₂ :=
  (evalMap V₁ V₂).comp
    (paired
      ((proj₀ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
        (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
      ((evalMap V₀ V₁).comp
        (paired
          ((proj₁ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
            (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
          (proj₁ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))))

end DomainTheory.NeighbourhoodSystems
