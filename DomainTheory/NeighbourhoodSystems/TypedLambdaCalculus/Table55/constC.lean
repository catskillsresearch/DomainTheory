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

/-- **Table 5.5 (Scott 1981, PRG-19).** `const = λk λx.k`, sending `k ∈ |𝒟₁|` to the constant map
`𝒟₀ → 𝒟₁`. Realized as `curry(p₀)`. -/
def constC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₁ (funSpace V₀ V₁) := curry (proj₀ V₁ V₀)

end DomainTheory.NeighbourhoodSystems
