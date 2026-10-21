/-ai
The while-loop element of the function space is the least fixed point of the operator Wop built from the test p and the body f.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.Wop

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise512

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- The `while`-loop element of the function space `D → D`: the least fixed point of `Wop`. -/
def whileFix : (funSpace V V).Element := (Wop V p f).fixElement

end DomainTheory.NeighbourhoodSystems.Exercise512
