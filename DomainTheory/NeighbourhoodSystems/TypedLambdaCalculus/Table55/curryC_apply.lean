module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.curryC_toApproxMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem curryC_apply (φ : (funSpace (prod V₀ V₁) V₂).Element) (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((toApproxMap ((curryC V₀ V₁ V₂).toElementMap φ)).toElementMap x)).toElementMap y
      = (toApproxMap φ).toElementMap (pair x y) := by
  rw [curryC_toApproxMap, toElementMap_curry_apply]

end DomainTheory.NeighbourhoodSystems
