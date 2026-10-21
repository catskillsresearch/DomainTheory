/-ai
The product of the universal domain with itself embeds in the universal domain.

The product injection and product projection of Definition 8.9 are a projection pair, and a projection pair determines an embedding.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.Basic

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Subsystemu2etrianglelefteq
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}


/-- **Exercise 8.17, Part 1 (`×`).** `iTimes/jTimes` already are the pair `𝒰×𝒰 ⇄ 𝒰`; bonus `⊴`. -/
theorem prodUU_trianglelefteq_U : prod U U ⊴ U :=
  trianglelefteq_of_projectionPair iTimes jTimes jTimes_comp_iTimes iTimes_comp_jTimes_le

end DomainTheory.NeighbourhoodSystems
