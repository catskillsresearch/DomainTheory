module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem pairC_apply (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((pairC V₀ V₁).toElementMap x)).toElementMap y = pair x y := by
  rw [pairC, toElementMap_curry_apply, toElementMap_idMap]

end DomainTheory.NeighbourhoodSystems
