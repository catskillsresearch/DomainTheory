/-ai
Every domain is a subdomain of its infinite power. Specialized to the universal domain, this is Scott's embedding of the universal domain into its infinite power.

Apply the projection-pair criterion to the singleton-stack embedding and the head, using that the head retracts the embedding and that the embedding after the head lies below the identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise618
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.head_comp_embedIntoPow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.embedIntoPow_comp_head_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 8.25 (Scott 1981, PRG-19): `𝒟 ⊴ 𝒟^∞`**, for every `𝒟`. Specialized to `𝒟 = 𝒰` this is
Scott's remark `𝒰 ⊴ 𝒰^∞`. -/
theorem trianglelefteq_iterSys : V ⊴ iterSys V :=
  trianglelefteq_of_projectionPair (embedIntoPow V) (head V)
    (head_comp_embedIntoPow V) (embedIntoPow_comp_head_le V)

end DomainTheory.NeighbourhoodSystems
