/-ai
Converting a strict map to the corresponding element of the strict function space and then back returns the original strict map.

This is the right inverse of the order equivalence between elements of the strict function space and strict maps.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe u





/-- `toStrictMap ∘ toStrictFilter = id` (the right inverse of the strict-function-space
representation, Exercise 5.10). -/
theorem toStrictMap_toStrictFilter {α β : Type*} {V₀ : NeighborhoodSystem α}
    {V₁ : NeighborhoodSystem β} (f : StrictMap V₀ V₁) :
    toStrictMap (toStrictFilter f) = f :=
  (strictFunEquiv V₀ V₁).right_inv f

end DomainTheory.NeighbourhoodSystems
