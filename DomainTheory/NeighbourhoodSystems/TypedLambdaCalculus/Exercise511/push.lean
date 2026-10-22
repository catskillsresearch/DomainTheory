module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.fold

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `push : D × D^∞ → D^∞`, prepend an element to a stack. -/
def push : ApproximableMap (prod V (iterSys V)) (iterSys V) := fold V

end DomainTheory.NeighbourhoodSystems.Exercise511
