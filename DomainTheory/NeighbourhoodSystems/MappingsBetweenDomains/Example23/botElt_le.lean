/-ai
The bottom element of T lies below every element of T.

A neighbourhood of bottom is the master neighbourhood, and every element contains the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example12
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.T
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23.botElt

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- `⊥` approximates every element of `T` (the local `{Δ}` form, proved directly). -/
theorem botElt_le (x : T.Element) : botElt ≤ x := by
  intro Z hZ
  have : Z = Example12.master := hZ
  subst this
  exact x.master_mem

end DomainTheory.NeighbourhoodSystems.Example23
