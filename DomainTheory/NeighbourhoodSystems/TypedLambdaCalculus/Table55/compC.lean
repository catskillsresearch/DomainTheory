module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₀_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₁_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.diagC_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.swapC_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.compMapTbl

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `comp = λg,f λx.g(f(x))` as an approximable map
`((𝒟₁→𝒟₂) × (𝒟₀→𝒟₁)) → (𝒟₀ → 𝒟₂)`. -/
def compC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) (funSpace V₀ V₂) :=
  curry (compMapTbl V₀ V₁ V₂)

end DomainTheory.NeighbourhoodSystems
