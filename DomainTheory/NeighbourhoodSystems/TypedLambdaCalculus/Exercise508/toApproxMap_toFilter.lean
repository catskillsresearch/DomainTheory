/-ai
Passing an approximable map through the filter representation of a function-space element and back returns the original map.

The function-space equivalence identifies the two directions on that map. Rewriting by those two directions gives the claim.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise508.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise508

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap


variable {α β γ : Type*}

/-- `toApproxMap ∘ toFilter = id`: the representation of a function-space *element* by an approximable
map is a left inverse of `toFilter` (this is `funSpaceEquiv` unfolded). -/
theorem toApproxMap_toFilter {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (f : ApproximableMap V₀ V₁) : toApproxMap (toFilter f) = f := by
  have he := (funSpaceEquiv V₀ V₁).apply_symm_apply f
  rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he

end DomainTheory.NeighbourhoodSystems.Exercise508
