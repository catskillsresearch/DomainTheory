module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₀_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₁_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.diagC_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.swapC_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.curryIso

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** `curry = λg λx λy.g(x,y)` as an approximable map
`(𝒟₀ × 𝒟₁ → 𝒟₂) → (𝒟₀ → (𝒟₁ → 𝒟₂))`. -/
def curryC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (funSpace (prod V₀ V₁) V₂) (funSpace V₀ (funSpace V₁ V₂)) :=
  ofIso (curryIso V₀ V₁ V₂)

end DomainTheory.NeighbourhoodSystems
