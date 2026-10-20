module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.unfold

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `head : D^∞ → D`, the top of the stack. -/
def head : ApproximableMap (iterSys V) V := (proj₀ V (iterSys V)).comp (unfold V)

end DomainTheory.NeighbourhoodSystems.Exercise511
