module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.bodyMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise512

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

open DomainTheory.NeighbourhoodSystems.Exercise326 (cond TD)

variable {α : Type*} (V : NeighborhoodSystem α)
  (p : ApproximableMap V TD) (f : ApproximableMap V V)

/-- The loop operator `Wop : (D → D) → (D → D)`, `Wop(w) = λx. cond(p(x), w(f(x)), x)`. -/
def Wop : ApproximableMap (funSpace V V) (funSpace V V) := curry (bodyMap V p f)

end DomainTheory.NeighbourhoodSystems.Exercise512
