module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise507.curry₃

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise507

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- The defining equation of `curry₃`: `(λx, y, z. g)(x)(y)(z) = g⟨⟨x, y⟩, z⟩`. -/
theorem curry₃_apply (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃)
    (x : V₀.Element) (y : V₁.Element) (z : V₂.Element) :
    (toApproxMap ((toApproxMap ((curry₃ g).toElementMap x)).toElementMap y)).toElementMap z =
      g.toElementMap (pair (pair x y) z) := by
  rw [curry₃, toElementMap_curry_apply, toElementMap_curry_apply]

end DomainTheory.NeighbourhoodSystems.Exercise507
