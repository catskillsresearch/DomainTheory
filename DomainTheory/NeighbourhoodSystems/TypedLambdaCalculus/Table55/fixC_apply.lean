module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.Basic

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixMap_toElementMap
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem fixC_apply (φ : (funSpace V V).Element) :
    (fixC V).toElementMap φ = (toApproxMap φ).fixElement := by
  rw [fixC, fixMap_toElementMap]

end DomainTheory.NeighbourhoodSystems
