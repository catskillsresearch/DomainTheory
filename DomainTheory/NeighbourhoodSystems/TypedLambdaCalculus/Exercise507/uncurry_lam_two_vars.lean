module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise507.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise507

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}




/-- The two encodings are mutually inverse: uncurrying the two-variable abstraction returns the
original two-variable function. -/
theorem uncurry_lam_two_vars (g : ApproximableMap (prod V₀ V₁) V₂) : uncurry (curry g) = g :=
  uncurry_curry g

end DomainTheory.NeighbourhoodSystems.Exercise507
