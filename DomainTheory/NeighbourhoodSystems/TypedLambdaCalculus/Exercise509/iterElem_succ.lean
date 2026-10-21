/-ai
The successor iterate of an approximable endomap from the bottom element is the element map applied to the preceding iterate.

Rewrite both iterates as function iteration and apply the successor law for iteration.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `f.iterElem (n+1) = f(fⁿ(⊥))`. -/
theorem iterElem_succ (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem (n + 1) = f.toElementMap (f.iterElem n) := by
  rw [iterElem_eq_iterate, iterElem_eq_iterate, Function.iterate_succ', Function.comp_apply]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
