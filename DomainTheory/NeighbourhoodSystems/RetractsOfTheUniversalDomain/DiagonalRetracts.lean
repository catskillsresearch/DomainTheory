module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_15
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Combinators

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.EmbeddingsIntoU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition_8_10
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SumProdRetracts
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} (D : NeighborhoodSystem α)

theorem exercise_8_20_assembly : D ⊴ prod D D ∧ D ⊴ funSpace D D :=
  ⟨D_trianglelefteq_prod D, D_trianglelefteq_funSpace D⟩
end

open NeighborhoodSystem ApproximableMap

theorem example_820 :
    (∀ {α : Type*} (D : NeighborhoodSystem α), D ⊴ prod D D ∧ D ⊴ funSpace D D) ∧
    (∀ {α : Type*} (D : NeighborhoodSystem α), D ⊴ funSpace D D) ∧
    (∀ {α : Type*} (D : NeighborhoodSystem α), D ⊴ prod D D) :=
  ⟨@exercise_8_20_assembly, @D_trianglelefteq_funSpace, @D_trianglelefteq_prod⟩

section
open NeighborhoodSystem ApproximableMap
universe u v

section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)

theorem trianglelefteq_prod_snd : B ⊴ prod A B :=
  trianglelefteq_of_projectionPair (embedSnd A B) (proj₁ A B) (proj₁_comp_embedSnd A B)
    (embedSnd_comp_proj₁_le A B)

end Prod
end

end DomainTheory.NeighbourhoodSystems
