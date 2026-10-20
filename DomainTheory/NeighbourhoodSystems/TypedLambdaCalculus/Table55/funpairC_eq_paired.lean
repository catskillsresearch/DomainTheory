module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.funpairC_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}



























/-- `funpair(f)(g)` is the paired map `⟨f, g⟩` of Definition 3.3. -/
theorem funpairC_eq_paired (φ : (funSpace V₂ V₀).Element) (ψ : (funSpace V₂ V₁).Element) :
    toApproxMap ((toApproxMap ((funpairC V₀ V₁ V₂).toElementMap φ)).toElementMap ψ)
      = paired (toApproxMap φ) (toApproxMap ψ) := by
  apply ext_of_toElementMap
  intro x
  rw [funpairC_apply, toElementMap_paired]

end DomainTheory.NeighbourhoodSystems
