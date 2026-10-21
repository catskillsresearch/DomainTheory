/-ai
Evaluation at a function-space element φ and an element x equals the map of φ at x.

Rewrite by the definition of the combinator and the evaluation map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
  {V : NeighborhoodSystem α} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


theorem evalC_apply (φ : (funSpace V₀ V₁).Element) (x : V₀.Element) :
    (evalC V₀ V₁).toElementMap (pair φ x) = (toApproxMap φ).toElementMap x := by
  rw [evalC, evalMap_apply]

end DomainTheory.NeighbourhoodSystems
