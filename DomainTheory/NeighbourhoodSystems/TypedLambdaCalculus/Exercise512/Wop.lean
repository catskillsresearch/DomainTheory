/-ai
The loop operator is the curry of the loop body for a predicate and an update, so that its value at a function is the function sending an element to the conditional of the predicate, the function applied after the update, and the element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.bodyMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise512

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- The loop operator `Wop : (D → D) → (D → D)`, `Wop(w) = λx. cond(p(x), w(f(x)), x)`. -/
def Wop : ApproximableMap (funSpace V V) (funSpace V V) := curry (bodyMap V p f)

end DomainTheory.NeighbourhoodSystems.Exercise512
