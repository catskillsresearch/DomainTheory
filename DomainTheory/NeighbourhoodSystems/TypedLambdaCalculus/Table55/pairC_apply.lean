module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₀
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₁
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.pairC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.diagC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.swapC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.evalC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.constC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.curryIso
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.curryC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.compMapTbl
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.compC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.funpairMapTbl
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.funpairC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.fixC
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₀_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.P₁_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.diagC_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.swapC_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem pairC_apply (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((pairC V₀ V₁).toElementMap x)).toElementMap y = pair x y := by
  rw [pairC, toElementMap_curry_apply, toElementMap_idMap]

end DomainTheory.NeighbourhoodSystems
