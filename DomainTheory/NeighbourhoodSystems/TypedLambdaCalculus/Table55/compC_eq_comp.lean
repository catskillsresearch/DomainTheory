/-ai
The map recovered from the composition combinator at a pair of function-space elements is the composition of the two corresponding approximable maps.

Extend by values. At each element, rewrite by the composition law and the application law of the combinator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.Basic
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
