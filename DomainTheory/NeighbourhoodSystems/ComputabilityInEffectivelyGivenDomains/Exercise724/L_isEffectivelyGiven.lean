/-ai
The LUCID neighbourhood system is effectively given.

The presentation of its enumeration is a witness.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive


/-- **Exercise 7.24 (i) — `L` is effectively given.** -/
theorem L_isEffectivelyGiven : L.IsEffectivelyGiven := ⟨Lpres⟩

end DomainTheory.NeighbourhoodSystems.Exercise724
