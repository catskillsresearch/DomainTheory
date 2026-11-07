module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.embeddingCompare

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise627
open NeighborhoodSystem Exercise619 SmashProduct ExampleB

theorem example_627 :
    (∀ (D₀ D₁ : NeighborhoodSystem Str), otimesTok D₀ D₁ ⊴ prodTok D₀ D₁) ∧
    (∀ {D₀ D₁ : NeighborhoodSystem Str} {h₀ : ∀ X, D₀.mem X → X.Nonempty}
        {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty},
      D₀ ⊴ oplusTok D₀ D₁ h₀ h₁) ∧
    (∀ (D₀ D₁ : NeighborhoodSystem Str), D₀ ⊴ prodTok D₀ D₁) ∧
    (¬ (twoPt ⊴ otimesTok twoPt unitPt)) ∧
    (∀ {D₀ D₁ : NeighborhoodSystem Str} (h₀ : ∀ X, D₀.mem X → X.Nonempty)
        (h₁ : ∀ Y, D₁.mem Y → Y.Nonempty),
      oplusTok D₀ D₁ h₀ h₁ ⊴ sumTok D₀ D₁ h₀ h₁) ∧
    (∀ {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β),
      strictFun V₀ V₁ ⊴ funSpace V₀ V₁) :=
  ⟨@otimes_trianglelefteq_prod, @inl_trianglelefteq_oplus, @fst_trianglelefteq_prod,
    @not_trianglelefteq_otimes, @oplus_trianglelefteq_sum, @strictFun_trianglelefteq_funSpace⟩

end DomainTheory.NeighbourhoodSystems.Exercise627
