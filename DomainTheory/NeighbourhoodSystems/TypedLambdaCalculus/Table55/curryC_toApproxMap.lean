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


/-- `curry(g)` is the curried map of Theorem 3.12. -/
theorem curryC_toApproxMap (φ : (funSpace (prod V₀ V₁) V₂).Element) :
    toApproxMap ((curryC V₀ V₁ V₂).toElementMap φ) = curry (toApproxMap φ) := by
  rw [curryC, toElementMap_ofIso]
  show toApproxMap (toFilter (curry (toApproxMap φ))) = curry (toApproxMap φ)
  have he := (funSpaceEquiv V₀ (funSpace V₁ V₂)).apply_symm_apply (curry (toApproxMap φ))
  rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he

end DomainTheory.NeighbourhoodSystems
