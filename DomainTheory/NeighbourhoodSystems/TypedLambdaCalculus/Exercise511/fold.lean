/-ai
Folding is the approximable map from the product of a neighbourhood system with its iteration back to the iteration, induced by the inverse of the product isomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `fold : D × D^∞ → D^∞`, the inverse direction of `iterProdIso`. -/
def fold : ApproximableMap (prod V (iterSys V)) (iterSys V) := ofIso (iterProdIso V).symm

end DomainTheory.NeighbourhoodSystems.Exercise511
