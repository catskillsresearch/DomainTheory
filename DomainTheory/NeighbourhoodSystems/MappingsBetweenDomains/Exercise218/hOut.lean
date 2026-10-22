module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- The guaranteed output of `h` on a finite prefix: each symbol `b` becomes the block `b0`. -/
def hOut : Str → Str
  | [] => []
  | b :: t => b :: false :: hOut t

end DomainTheory.NeighbourhoodSystems.Exercise218
