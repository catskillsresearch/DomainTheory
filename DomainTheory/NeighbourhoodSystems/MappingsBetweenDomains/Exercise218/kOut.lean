module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_nil
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hOut_cons

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- The guaranteed output of `k` on a finite prefix: keep the first bit of every *complete* pair,
discard the inserted `0`. A trailing odd bit is an incomplete pair, hence dropped. -/
def kOut : Str → Str
  | [] => []
  | [_] => []
  | b :: _ :: t => b :: kOut t

end DomainTheory.NeighbourhoodSystems.Exercise218
