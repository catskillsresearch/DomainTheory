/-ai
The map operator is the curry of the map body, sending a function of a stack of functions and a point to the function that pushes the head function applied to the point onto the recursive value at the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.head_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.tail_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.Arg
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.mapBody

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The `map` recursion operator `R(W) = λ⟨s, x⟩. push((head s)(x), W(tail s, x))`. -/
def mapOp : ApproximableMap (funSpace (Arg V) (iterSys V)) (funSpace (Arg V) (iterSys V)) :=
  curry (mapBody V)

end DomainTheory.NeighbourhoodSystems.Exercise511
