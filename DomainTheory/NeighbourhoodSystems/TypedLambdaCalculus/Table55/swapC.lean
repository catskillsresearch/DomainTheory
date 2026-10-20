module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₀_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₁_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.diagC_apply

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- **Table 5.5 (Scott 1981, PRG-19).** The base case `inv_{0,1}^2 = λx,y.⟨y,x⟩` of the
argument-swap scheme: `𝒟₀ × 𝒟₁ → 𝒟₁ × 𝒟₀`. -/
def swapC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod V₀ V₁) (prod V₁ V₀) := paired (proj₁ V₀ V₁) (proj₀ V₀ V₁)

end DomainTheory.NeighbourhoodSystems
