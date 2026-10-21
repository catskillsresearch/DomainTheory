/-ai
The doubled output of a finite string is empty on the empty string, and on a string starting with a bit it writes that bit, then false, then the doubled output of the tail.
ai-/
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
