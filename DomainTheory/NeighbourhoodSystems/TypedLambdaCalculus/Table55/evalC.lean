/-ai
The evaluation combinator of Table 5.5 (Scott 1981, PRG-19) is the evaluation map from a product of a function space with its domain into the codomain.
ai-/
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

/-- **Table 5.5 (Scott 1981, PRG-19).** `eval = λf,x.f(x)`, evaluation `(𝒟₀ → 𝒟₁) × 𝒟₀ → 𝒟₁`
(this is Theorem 3.11's `evalMap`). -/
def evalC (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (prod (funSpace V₀ V₁) V₀) V₁ := evalMap V₀ V₁

end DomainTheory.NeighbourhoodSystems
