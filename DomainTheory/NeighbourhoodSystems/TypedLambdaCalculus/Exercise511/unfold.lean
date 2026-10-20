module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `unfold : D^∞ → D × D^∞`, the forward direction of `iterProdIso`. -/
def unfold : ApproximableMap (iterSys V) (prod V (iterSys V)) := ofIso (iterProdIso V)

end DomainTheory.NeighbourhoodSystems.Exercise511
