/-ai
The curry isomorphism sends a filter of the function space out of the product to the filter of the curry of its least approximable map.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise716.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}


/-- `curryIso V₀ V₁ V₂` sends a filter `x` to the filter of the curried least map (by definition). -/
theorem curryIso_apply (x : (funSpace (prod V₀ V₁) V₂).Element) :
    curryIso V₀ V₁ V₂ x = toFilter (curry (toApproxMap x)) := rfl

end DomainTheory.NeighbourhoodSystems
