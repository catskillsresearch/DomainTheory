module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


















theorem constC_apply (k : V₁.Element) (x : V₀.Element) :
    (toApproxMap ((constC V₀ V₁).toElementMap k)).toElementMap x = k := by
  rw [constC, toElementMap_curry_apply, toElementMap_proj₀, fst_pair]

end DomainTheory.NeighbourhoodSystems
