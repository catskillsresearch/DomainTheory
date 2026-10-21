/-ai
The constant stack is the composite of the fixed-point combinator on the iteration with the curry of push, so that its value at an element is the least stack equal to that element pushed onto itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.push
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.head_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.tail_apply

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `diag : D → D^∞`, defined as the least fixed point of `s ↦ push(x, s)`. -/
def diag : ApproximableMap V (iterSys V) :=
  (fixMap (iterSys V)).comp (curry (push V))

end DomainTheory.NeighbourhoodSystems.Exercise511
