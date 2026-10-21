/-ai
Applying a map out of a product to a pair equals applying its curried form to the first component and then to the second. The right-hand side uses only application to one argument.

Rewrite by the equation for the element map of a curry.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise507.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise507

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- The combinator `σ(x, y)` (apply `σ : D₀ × D₁ → D₂` to two arguments) is expressed through the
*one-variable* curried form: `σ(⟨x, y⟩) = (curry σ)(x)(y)`. The right-hand side uses only
single-variable application. -/
theorem app_two_args (σ : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    σ.toElementMap (pair x y) =
      (toApproxMap ((curry σ).toElementMap x)).toElementMap y := by
  rw [toElementMap_curry_apply]

end DomainTheory.NeighbourhoodSystems.Exercise507
