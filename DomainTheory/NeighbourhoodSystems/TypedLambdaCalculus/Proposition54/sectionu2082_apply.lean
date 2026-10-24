module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition54.section₂
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition54.pfix
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition54.recOp

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


theorem section₂_apply (τ : ApproximableMap (prod V V) V) (x y : V.Element) :
    (section₂ τ x).toElementMap y = τ.toElementMap (pair x y) := by
  rw [section₂, toElementMap_curry_apply]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
