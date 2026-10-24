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


theorem funpairC_apply (φ : (funSpace V₂ V₀).Element) (ψ : (funSpace V₂ V₁).Element)
    (x : V₂.Element) :
    (toApproxMap ((toApproxMap ((funpairC V₀ V₁ V₂).toElementMap φ)).toElementMap ψ)).toElementMap x
      = pair ((toApproxMap φ).toElementMap x) ((toApproxMap ψ).toElementMap x) := by
  rw [funpairC, toElementMap_curry_apply, toElementMap_curry_apply, funpairMapTbl]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

end DomainTheory.NeighbourhoodSystems
