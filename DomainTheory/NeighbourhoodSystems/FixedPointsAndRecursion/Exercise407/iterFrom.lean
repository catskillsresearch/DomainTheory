module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The chain of approximants from a base point `a`: `iterFrom f a n = fⁿ(a)`. -/
def iterFrom (f : ApproximableMap V V) (a : V.Element) (n : ℕ) : V.Element :=
  (f.toElementMap)^[n] a

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
