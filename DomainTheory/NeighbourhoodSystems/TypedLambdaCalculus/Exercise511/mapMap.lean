/-ai
The map combinator is the approximable map denoted by the least fixed point of the map operator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.head_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.tail_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.Arg
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.mapOp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `map : (D → D)^∞ × D → D^∞`, the least fixed point of `mapOp`. -/
def mapMap : ApproximableMap (Arg V) (iterSys V) := toApproxMap (mapOp V).fixElement

end DomainTheory.NeighbourhoodSystems.Exercise511
