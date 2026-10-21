/-ai
The curry isomorphism is the order isomorphism from the function space of a product into a codomain to the iterated function space, obtained by composing the function-space equivalence, the curry equivalence, and the inverse function-space equivalence.
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

/-- The order-isomorphism `|𝒟₀ × 𝒟₁ → 𝒟₂| ≃o |𝒟₀ → (𝒟₁ → 𝒟₂)|` between the *function-space
domains*, obtained from Theorem 3.10 (`funSpaceEquiv`) and Theorem 3.12 (`curryEquiv`). -/
def curryIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    (funSpace (prod V₀ V₁) V₂).Element ≃o (funSpace V₀ (funSpace V₁ V₂)).Element :=
  (funSpaceEquiv (prod V₀ V₁) V₂).trans
    ((curryEquiv V₀ V₁ V₂).trans (funSpaceEquiv V₀ (funSpace V₁ V₂)).symm)

end DomainTheory.NeighbourhoodSystems
