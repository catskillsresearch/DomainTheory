/-ai
The value of τ at the pair of x with the left-hand map of τ at x equals that left-hand value.

Rewrite by the application law of the left-hand map, the application law of the section, and the fixed-point equation of the section.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition54.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition54.sectionu2082_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition54.pfix_apply

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.toElementMap_fixElement
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap




/-- `pfix τ` is a fixed point of `recOp τ` (pointwise: `τ(x, pfix τ x) = pfix τ x`). -/
theorem pfix_isFixed (τ : ApproximableMap (prod V V) V) (x : V.Element) :
    τ.toElementMap (pair x ((pfix τ).toElementMap x)) = (pfix τ).toElementMap x := by
  rw [pfix_apply, ← section₂_apply, toElementMap_fixElement]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
