/-ai
The zero-th iterate of an approximable endomap from the bottom element is the bottom element.

Rewrite the iterate as function iteration. The zero-fold iterate is the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterElem_eq_iterate
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem iterElem_zero' (f : ApproximableMap V V) : f.iterElem 0 = V.bot := by
  rw [iterElem_eq_iterate, Function.iterate_zero_apply]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
