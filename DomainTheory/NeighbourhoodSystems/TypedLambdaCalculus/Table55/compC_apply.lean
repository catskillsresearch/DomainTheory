module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem compC_apply (φ : (funSpace V₁ V₂).Element) (ψ : (funSpace V₀ V₁).Element) (x : V₀.Element) :
    (toApproxMap ((compC V₀ V₁ V₂).toElementMap (pair φ ψ))).toElementMap x
      = (toApproxMap φ).toElementMap ((toApproxMap ψ).toElementMap x) := by
  rw [compC, toElementMap_curry_apply, compMapTbl]
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

end DomainTheory.NeighbourhoodSystems
