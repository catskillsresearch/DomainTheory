/-ai
The approximable map recovered from the recursion operator of τ at a function-space element φ sends x to the value of τ at the pair of x with the map of φ at x.

Rewrite by the definition of the operator, the curried application law, the composition law, the pairing law, the second projection, the second component of a pair, and evaluation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition54.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap




/-- `recOp τ (g) (x) = τ(x, g(x))`. -/
theorem recOp_apply (τ : ApproximableMap (prod V V) V) (φ : (funSpace V V).Element) (x : V.Element) :
    (toApproxMap ((recOp τ).toElementMap φ)).toElementMap x
      = τ.toElementMap (pair x ((toApproxMap φ).toElementMap x)) := by
  rw [recOp, toElementMap_curry_apply, toElementMap_comp, toElementMap_paired,
    toElementMap_proj₁, snd_pair, evalMap_apply]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
