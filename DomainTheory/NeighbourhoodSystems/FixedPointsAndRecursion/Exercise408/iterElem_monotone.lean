/-ai
The approximants of an approximable endomap, starting from bottom, form a monotone chain indexed by the natural numbers.

Monotonicity is the comparison of approximants already given for an inequality of indices.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise408.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The approximants form a monotone `ω`-chain (the `Monotone` packaging of `iterElem_mono`). -/
theorem iterElem_monotone (f : ApproximableMap V V) : Monotone f.iterElem :=
  fun _ _ hab => iterElem_mono f hab

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
