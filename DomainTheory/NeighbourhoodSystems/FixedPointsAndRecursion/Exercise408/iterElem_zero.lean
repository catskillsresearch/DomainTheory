/-ai
The zero-th approximant of an approximable endomap is the bottom element.

It is the elementwise action of the identity map at bottom.
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


theorem iterElem_zero (f : ApproximableMap V V) : f.iterElem 0 = V.bot :=
  toElementMap_idMap V.bot

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
