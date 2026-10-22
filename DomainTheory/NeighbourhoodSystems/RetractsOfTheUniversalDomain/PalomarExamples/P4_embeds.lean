module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.PalomarExamples.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example15

/-- **New corollary for Example 1.5.** The finite powerset system is countable, so the first
sentence of Theorem 8.8 applies. Scott does not separately state this embedding. -/
theorem P4_embeds : neighborhoodSystem ⊴ U :=
  theorem_8_8 neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example15
