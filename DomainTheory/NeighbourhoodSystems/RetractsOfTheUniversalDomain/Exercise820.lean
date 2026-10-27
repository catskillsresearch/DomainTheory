module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_15
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table_5_5

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.EmbeddingsIntoU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition_8_10
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} (D : NeighborhoodSystem α)
/- concordance: source L5185 EXERCISE 8.20 self-embeddings of a domain -/
/-- **Exercise 8.20.** For any domain `D`, `D ⊴ D×D` and `D ⊴ D→D` (unconditionally — no hypotheses
needed, unlike Exercise 8.19). See the module docstring for the discussion of computability and
multiplicity of projection pairs that Scott also asks about. -/
theorem exercise_8_20_assembly : D ⊴ prod D D ∧ D ⊴ funSpace D D :=
  ⟨D_trianglelefteq_prod D, D_trianglelefteq_funSpace D⟩
end

section
set_option linter.unusedVariables false

theorem example_820.{u} : And
  (And
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      And
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq α (Sum α α) D
          (@DomainTheory.NeighbourhoodSystems.prod α α D D))
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
          (@DomainTheory.NeighbourhoodSystems.funSpace α α D D)))
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq α (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
        (@DomainTheory.NeighbourhoodSystems.funSpace α α D D)))
  (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq α (Sum α α) D (@DomainTheory.NeighbourhoodSystems.prod α α D D)) :=
  @And.intro
  (And
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      And
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq α (Sum α α) D
          (@DomainTheory.NeighbourhoodSystems.prod α α D D))
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
          (@DomainTheory.NeighbourhoodSystems.funSpace α α D D)))
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq α (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
        (@DomainTheory.NeighbourhoodSystems.funSpace α α D D)))
  (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq α (Sum α α) D (@DomainTheory.NeighbourhoodSystems.prod α α D D))
  (@And.intro
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      And
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq α (Sum α α) D
          (@DomainTheory.NeighbourhoodSystems.prod α α D D))
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq α
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
          (@DomainTheory.NeighbourhoodSystems.funSpace α α D D)))
    (∀ {α : Type u} (D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq α (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
        (@DomainTheory.NeighbourhoodSystems.funSpace α α D D))
    @DomainTheory.NeighbourhoodSystems.exercise_8_20_assembly @DomainTheory.NeighbourhoodSystems.D_trianglelefteq_funSpace)
  @DomainTheory.NeighbourhoodSystems.D_trianglelefteq_prod
end

section
open NeighborhoodSystem ApproximableMap
universe u v

section Prod

variable {α : Type u} {β : Type v} (A : NeighborhoodSystem α) (B : NeighborhoodSystem β)


/-- **`B ⊴ prod A B`**, via `b ↦ ⟨⊥, b⟩` / `proj₁`. -/
theorem trianglelefteq_prod_snd : B ⊴ prod A B :=
  trianglelefteq_of_projectionPair (embedSnd A B) (proj₁ A B) (proj₁_comp_embedSnd A B)
    (embedSnd_comp_proj₁_le A B)

end Prod
end

end DomainTheory.NeighbourhoodSystems
end
