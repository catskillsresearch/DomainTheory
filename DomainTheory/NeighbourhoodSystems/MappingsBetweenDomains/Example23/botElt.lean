/-ai
The bottom element of T is the bottom element of the two-token system, the partial element whose only neighbourhood is the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.T

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Scott's `⊥`: the unique partial element `{Δ}` of `T`. -/
def botElt : T.Element := Example12.neighborhoodSystem.bot

end DomainTheory.NeighbourhoodSystems.Example23
