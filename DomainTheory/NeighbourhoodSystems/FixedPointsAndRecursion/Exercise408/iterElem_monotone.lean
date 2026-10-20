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
