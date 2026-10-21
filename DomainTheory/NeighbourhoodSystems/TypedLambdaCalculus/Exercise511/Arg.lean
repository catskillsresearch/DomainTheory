/-ai
The argument domain of the map combinator is the product of the iterated function space with the underlying neighbourhood system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.head_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.tail_apply

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The argument domain of `map`: a stack of functions paired with a point, `(D → D)^∞ × D`. -/
abbrev Arg (V : NeighborhoodSystem α) := prod (iterSys (funSpace V V)) V

end DomainTheory.NeighbourhoodSystems.Exercise511
