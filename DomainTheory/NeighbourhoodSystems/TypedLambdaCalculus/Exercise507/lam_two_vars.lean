/-ai
Two-variable abstraction is currying: applying the curry of a map to x and then to y equals applying the map to the pair of x and y.

This is the equation for the element map of a curry.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise507.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise507

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}




/-- **Two-variable abstraction.** `λx, y. τ` is `curry`, characterised by `(curry g)(x)(y) = g⟨x, y⟩`.
It binds one variable `x` and returns the one-variable function `λy. g⟨x, y⟩`. -/
theorem lam_two_vars (g : ApproximableMap (prod V₀ V₁) V₂) (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((curry g).toElementMap x)).toElementMap y = g.toElementMap (pair x y) :=
  toElementMap_curry_apply g x y

end DomainTheory.NeighbourhoodSystems.Exercise507
