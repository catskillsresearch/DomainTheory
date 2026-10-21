/-ai
The tail of a stack is the second projection of its unfolding.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.unfold

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `tail : D^∞ → D^∞`, the stack with its top removed. -/
def tail : ApproximableMap (iterSys V) (iterSys V) := (proj₁ V (iterSys V)).comp (unfold V)

end DomainTheory.NeighbourhoodSystems.Exercise511
