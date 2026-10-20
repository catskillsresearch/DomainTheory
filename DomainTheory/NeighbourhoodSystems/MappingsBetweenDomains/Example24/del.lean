module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.SatisfiesRunEquations

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Inside the first run of `1`'s: swallow `1`'s; on the first `0`, emit it and copy the rest. -/
def del : Str → Str
  | [] => []
  | true :: t => del t
  | false :: t => false :: t

end DomainTheory.NeighbourhoodSystems.Example24
