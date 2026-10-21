/-ai
The neighbourhood system S embeds into the universal domain.

Apply the first sentence of Theorem 8.8 to S. Countability of its neighbourhoods is the instance already recorded for S.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example15
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.PalomarExamples.Basic

@[expose] public section



namespace DomainTheory.NeighbourhoodSystems.Exercise722


/-- **New corollary for Exercise 7.22.** Countability is `Ssys_countable` (via `SExpr`), so the
first sentence of Theorem 8.8 applies. Scott does not separately state this embedding. -/
theorem Ssys_embeds : Ssys ⊴ U :=
  theorem_8_8 Ssys

end DomainTheory.NeighbourhoodSystems.Exercise722
