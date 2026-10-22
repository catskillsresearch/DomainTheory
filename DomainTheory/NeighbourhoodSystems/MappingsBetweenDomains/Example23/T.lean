module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- The two-token codomain `T` of Example 1.2. -/
abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example23
