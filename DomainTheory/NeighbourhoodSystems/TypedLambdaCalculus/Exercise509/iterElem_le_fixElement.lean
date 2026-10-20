module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise509.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `fⁿ(⊥) ⊑ fix(f)`. -/
theorem iterElem_le_fixElement (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem n ≤ f.fixElement := by
  rw [fixElement_eq_iSupDirected f]
  exact NeighborhoodSystem.le_iSupDirected f.iterElem _ n

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
