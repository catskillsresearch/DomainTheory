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
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.compC_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- `comp(g, f) = g ∘ f` (Scott's infix `g ∘ f`). -/
theorem compC_eq_comp (φ : (funSpace V₁ V₂).Element) (ψ : (funSpace V₀ V₁).Element) :
    toApproxMap ((compC V₀ V₁ V₂).toElementMap (pair φ ψ)) = (toApproxMap φ).comp (toApproxMap ψ) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, compC_apply]

end DomainTheory.NeighbourhoodSystems
