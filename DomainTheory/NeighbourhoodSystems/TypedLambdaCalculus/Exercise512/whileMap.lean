/-ai
The approximable map while p do f is the approximable map denoted by the while-loop element, the least fixed point of Wop.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.whileFix

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise512

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- The approximable function `while p do f : D → D` denoted by `whileFix`. -/
def whileMap : ApproximableMap V V := toApproxMap (whileFix V p f)

end DomainTheory.NeighbourhoodSystems.Exercise512
